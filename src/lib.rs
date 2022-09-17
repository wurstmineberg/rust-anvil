//! A library for working with Minecraft's region format, Anvil.
//!
//! The main entry point is `Region::open`.

#![deny(missing_docs, rust_2018_idioms, unused, unused_import_braces, unused_qualifications, warnings)]

use {
    std::{
        fmt,
        fs::File,
        io::{
            self,
            SeekFrom,
            prelude::*,
        },
        num::ParseIntError,
        path::Path,
    },
    lazy_regex::regex_captures,
    serde::Deserialize,
};

mod biome;

pub use biome::Biome;

/// An error returned by `Region::open`.
#[derive(Debug, thiserror::Error)]
pub enum RegionDecodeError {
    /// The given filename did not match the region coordinates format, `r.<x>.<z>.mca`.
    #[error("the given filename did not match the region coordinates format, `r.<x>.<z>.mca`")]
    InvalidFileName,
    #[allow(missing_docs)] #[error(transparent)] Io(#[from] io::Error),
    /// The x or z coordinate did not fit into an `i32`.
    #[error(transparent)] ParseInt(#[from] ParseIntError),
}

/// A region is a section of a world that's stored as a single `.mca` file, consisting of 32×32 chunk columns.
pub struct Region {
    /// The region coordinates of this region, i.e. the block coordinates of its northwesternmost block column divided by 512.
    pub coords: [i32; 2],
    locations: [(u32, u8); 1024],
    //timestamps: [u32; 1024],
    file: File,
}

impl Region {
    /// Opens the given `.mca` file and parses it as a `Region`.
    ///
    /// # Errors
    ///
    /// See the `RegionDecodeError` docs.
    pub fn open(path: impl AsRef<Path>) -> Result<Region, RegionDecodeError> {
        let (_, rx, rz) = regex_captures!("^r\\.(-?[0-9]+)\\.(-?[0-9]+)\\.mca$", path.as_ref().file_name().ok_or(RegionDecodeError::InvalidFileName)?.to_str().ok_or(RegionDecodeError::InvalidFileName)?).ok_or(RegionDecodeError::InvalidFileName)?;
        let coords = [rx.parse()?, rz.parse()?];
        let mut file = File::open(path)?;
        let mut locations = [(0, 0); 1024];
        for i in 0..1024 {
            let mut offset = [0; 3];
            file.read_exact(&mut offset)?;
            let [o0, o1, o2] = offset;
            let offset = u32::from_be_bytes([0, o0, o1, o2]);
            let mut sector_count = [0; 1];
            file.read_exact(&mut sector_count)?;
            let [sector_count] = sector_count;
            locations[i] = (offset, sector_count);
        }
        let mut timestamps = [0; 1024];
        for i in 0..1024 {
            let mut timestamp = [0; 4];
            file.read_exact(&mut timestamp)?;
            timestamps[i] = u32::from_be_bytes(timestamp);
        }
        Ok(Region { coords, locations, /*timestamps,*/ file })
    }

    /// Returns a `ChunkColumn` in this region given its **absolute** chunk coordinates (i.e. the block coordinates of its northwesternmost block divided by 16).
    pub fn chunk_column(&self, [x, z]: [i32; 2]) -> Result<Option<ChunkColumn>, ChunkColumnDecodeError> {
        let x_offset = x & 31; //TODO make sure coords are in this region
        let z_offset = z & 31; //TODO make sure coords are in this region
        self.chunk_column_relative([x_offset as u8, z_offset as u8])
    }

    /// Returns a `ChunkColumn` in this region given its chunk coordinates (i.e. the block coordinates of its northwesternmost block divided by 16) **relative** to the northwest corner of this region.
    ///
    /// # Panics
    ///
    /// Panics if either of the given coordinates is not less than 32.
    pub fn chunk_column_relative(&self, [x_offset, z_offset]: [u8; 2]) -> Result<Option<ChunkColumn>, ChunkColumnDecodeError> {
        assert!(x_offset < 32 && z_offset < 32);
        let coords = [self.coords[0] * 32 + x_offset as i32, self.coords[1] * 32 + z_offset as i32];
        let (offset, sector_count) = self.locations[x_offset as usize + z_offset as usize * 32];
        if offset == 0 { return Ok(None) }
        (&self.file).seek(SeekFrom::Start(4096 * u64::from(offset))).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("seek", e) })?;
        // The Minecraft wiki says:
        // > Minecraft always pads the last chunk's data to be a multiple-of-4096B in length
        // But this seems to no longer be the case in Minecraft 1.16.1, so this implementation simply reads until EOF if the remaining file is shorter than indicated by sector_count.
        let mut data = Vec::default();
        (&self.file).take(4096 * sector_count as u64).read_to_end(&mut data).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("read chunk column", e) })?;
        Ok(Some(ChunkColumn::new(coords, data)?))
    }
}

impl fmt::Debug for Region {
    /// Omits the fields containing large amounts of raw bytes, which is currently all of them.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Region")
            .field("coords", &self.coords)
            .finish() //TODO (https://github.com/rust-lang/rust/issues/67364) replace with .finish_non_exhaustive()
    }
}

impl<'a> IntoIterator for &'a Region {
    type IntoIter = RegionIter<'a>;
    type Item = Result<ChunkColumn, ChunkColumnDecodeError>;

    fn into_iter(self) -> RegionIter<'a> {
        RegionIter {
            region: self,
            x_offset: 0,
            z_offset: 0,
        }
    }
}

/// An iterator over the chunk columns in a region, obtained using `&Region`'s implementation of the `IntoIterator` trait.
pub struct RegionIter<'a> {
    region: &'a Region,
    x_offset: u8,
    z_offset: u8,
}

impl<'a> Iterator for RegionIter<'a> {
    type Item = Result<ChunkColumn, ChunkColumnDecodeError>;

    fn next(&mut self) -> Option<Result<ChunkColumn, ChunkColumnDecodeError>> {
        loop {
            let old_offsets = [self.x_offset, self.z_offset];
            self.x_offset += 1;
            if self.x_offset >= 32 {
                self.z_offset += 1;
                self.x_offset = 0;
            }
            if self.z_offset >= 32 { return None }
            match self.region.chunk_column_relative(old_offsets) {
                Ok(Some(col)) => return Some(Ok(col)),
                Ok(None) => {}
                Err(e) => return Some(Err(e)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(32 * 32))
    }
}

/// An error returned by functions that construct `ChunkColumn`s.
#[derive(Debug)]
pub struct ChunkColumnDecodeError {
    /// The chunk coordinates where the error occurred.
    pub coords: [i32; 2],
    /// Information about what kind of error occurred.
    pub kind: ChunkColumnDecodeErrorKind,
}

/// The contents of a `ChunkColumnDecodeError`.
#[derive(Debug)]
pub enum ChunkColumnDecodeErrorKind {
    #[allow(missing_docs)]
    Io(&'static str, io::Error),
    #[allow(missing_docs)]
    Nbt(nbt::Error),
    /// Chunk columns are stored using different types of compression inside `.mca` files. The following compression types are currently implemented:
    ///
    /// 1. gzip
    /// 2. zlib
    ///
    /// If a chunk column with a different compression type is encountered, this error is returned, containing the compression type ID.
    UnknownCompressionType(u8),
}

/// A chunk column represents 16 chunks stacked vertically, or 16×256×16 blocks.
#[derive(Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct ChunkColumn {
    /// The format of `level` may have different semantics depending on this value.
    pub data_version: i32,
    /// The data of this chunk column, with contents depending on `data_version`.
    pub level: ChunkLevel,
}

/// The contents of the `level` field of a `ChunkColumn`.
#[derive(Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct ChunkLevel {
    /// The x chunk coordinate of this chunk, i.e. the block coordinates of its westernmost blocks divided by 16.
    #[serde(rename = "xPos")]
    pub x_pos: i32,
    /// The z chunk coordinate of this chunk, i.e. the block coordinates of its northernmost blocks divided by 16.
    #[serde(rename = "zPos")]
    pub z_pos: i32,
    /// `None` for chunks that haven't had biomes generated for them yet.
    biomes: Option<Vec<i32>>,
}

impl ChunkColumn {
    fn new(coords: [i32; 2], data: Vec<u8>) -> Result<ChunkColumn, ChunkColumnDecodeError> {
        let mut data_cursor = &*data;
        let mut len = [0; 4];
        data_cursor.read_exact(&mut len).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("read compressed length", e) })?;
        let len = u32::from_be_bytes(len) - 1;
        let mut compression = [0; 1];
        data_cursor.read_exact(&mut compression).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("read compression type", e) })?;
        Ok(match compression {
            [1] => nbt::from_gzip_reader(data_cursor.take(len as u64)).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Nbt(e) })?,
            [2] => nbt::from_zlib_reader(data_cursor.take(len as u64)).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Nbt(e) })?,
            [compression] => return Err(ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::UnknownCompressionType(compression) }),
        })
    }

    fn coords_to_relative(&self, [x, y, z]: [i32; 3]) -> Result<[u8; 3], [i32; 3]> {
        if x >= self.level.x_pos << 4 && x < (self.level.x_pos + 1) << 4 && y >= 0 && y < 256 && z >= self.level.z_pos << 4 && z < (self.level.z_pos + 1) << 4 {
            Ok([x as u8 & 15, y as u8, z as u8 & 15])
        } else {
            Err([x, y, z])
        }
    }

    /// Returns the biomes for all blocks in this chunk column. Blocks are grouped as west-east rows in north-south layers in a bottom-top column.
    ///
    /// # Errors
    ///
    /// If any block has an unknown biome ID, `Err` is returned with `Some` of the ID. This can happen if new biomes are added to Minecraft and this library is not yet updated.
    ///
    /// If the chunk does not have the `Biomes` tag, `Err(None)` is returned. This can happen for a chunk on the edge of the generated world where the biomes haven't been generated.
    pub fn biomes(&self) -> Result<[[[Biome; 16]; 16]; 256], Option<i32>> {
        let biomes = if let Some(ref biomes) = self.level.biomes {
            biomes
        } else {
            return Err(None)
        };
        let mut buf = [[[Biome::Ocean; 16]; 16]; 256];
        for (i, &bid) in biomes.iter().enumerate() {
            let biome = Biome::from_id(bid).ok_or(Some(bid))?;
            if biomes.len() == 1024 { // starting in 19w36a, biomes are stored per 4×4×4 cube
                let y = (i >> 4) * 4;
                let z = i & 0xc;
                let x = (i & 0x3) * 4;
                for y in y..y + 4 {
                    for z in z..z + 4 {
                        for x in x..x + 4 {
                            buf[y][z][x] = biome;
                        }
                    }
                }
            } else { // before 19w36a, biomes were stored per block column
                let z = i >> 4;
                let x = i & 15;
                for y in 0..256 {
                    buf[y][z][x] = biome;
                }
            }
        }
        Ok(buf)
    }

    /// Returns the [biome](https://minecraft.gamepedia.com/Biome) at the given block.
    ///
    /// # Errors
    ///
    /// If the block has an unknown biome ID, `Err` is returned with `Some` of the ID. This can happen if new biomes are added to Minecraft and this library is not yet updated.
    ///
    /// If the chunk does not have the `Biomes` tag, `Err(None)` is returned. This can happen for a chunk on the edge of the generated world where the biomes haven't been generated.
    ///
    /// # Panics
    ///
    /// This method panics if the coordinates are not in this chunk column (including a y coordinate below 0 or above 255).
    pub fn biome_at(&self, coords: [i32; 3]) -> Result<Biome, Option<i32>> {
        let biomes = if let Some(ref biomes) = self.level.biomes {
            biomes
        } else {
            return Err(None)
        };
        let [x, y, z] = self.coords_to_relative(coords).expect("coordinates out of bounds");
        let id = biomes[if biomes.len() == 1024 { // starting in 19w36a, biomes are stored per 4×4×4 cube
            ((y as usize >> 2) << 4) + ((z as usize >> 2) << 2) + (x as usize >> 2)
        } else { // before 19w36a, biomes were stored per block column
            ((z as usize) << 4) + x as usize
        }];
        Biome::from_id(id).ok_or(Some(id))
    }
}

#[test]
fn test_weird_region() {
    Region::open("assets\\r.11.-5.mca").unwrap().chunk_column([372, -132]).unwrap();
}
