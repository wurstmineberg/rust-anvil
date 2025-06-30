//! A library for working with Minecraft's region format, Anvil.
//!
//! The main entry point is `Region::open`.

use {
    std::{
        array,
        borrow::Cow,
        collections::HashMap,
        fmt,
        mem,
        num::ParseIntError,
        path::{
            Path,
            PathBuf,
        },
        time::Duration,
    },
    arrayref::array_ref,
    chrono::prelude::*,
    futures::{
        future,
        stream::{
            self,
            Stream,
            StreamExt as _,
            TryStreamExt as _,
        },
    },
    itertools::Itertools as _,
    lazy_regex::regex_captures,
    serde::Deserialize,
    serde_with::{
        DisplayFromStr,
        serde_as,
    },
    tokio::{
        fs::{
            self,
            File,
        },
        io::AsyncReadExt as _,
        time::sleep,
    },
};
#[cfg(feature = "async-proto")] use async_proto::Protocol;

mod biome;
mod block;

pub use crate::{
    biome::Biome,
    block::BlockId,
};

/// A [dimension](https://minecraft.wiki/w/Dimension).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "async-proto", derive(Protocol))]
pub enum Dimension {
    /// The [Overworld](https://minecraft.wiki/w/Overworld).
    #[default]
    Overworld,
    /// The [Nether](https://minecraft.wiki/w/The_Nether).
    Nether,
    /// The [End](https://minecraft.wiki/w/The_End).
    End,
}

/// An error returned by `Region::open`.
#[derive(Debug, thiserror::Error)]
pub enum RegionDecodeError {
    /// The given filename did not match the region coordinates format, `r.<x>.<z>.mca`.
    #[error("the given filename did not match the region coordinates format, `r.<x>.<z>.mca`")]
    InvalidFileName,
    #[allow(missing_docs)] #[error(transparent)] Io(#[from] tokio::io::Error),
    /// The x or z coordinate did not fit into an `i32`.
    #[error(transparent)] ParseInt(#[from] ParseIntError),
}

/// A region is a section of a world that's stored as a single `.mca` file, consisting of 32×32 chunk columns.
pub struct Region {
    /// The region coordinates of this region, i.e. the block coordinates of its northwesternmost block column divided by 512.
    pub coords: [i32; 2],
    locations: [(u32, u8); 1024],
    /// The last modification times of the chunks, listed north-to-south in west-to-east rows of chunks.
    pub timestamps: [DateTime<Utc>; 1024],
    /// The underlying buffer.
    pub buf: Vec<u8>,
}

impl Region {
    /// Opens the given `.mca` file and parses it as a `Region`.
    ///
    /// # Errors
    ///
    /// See the `RegionDecodeError` docs.
    pub async fn open(path: impl AsRef<Path>) -> Result<Region, RegionDecodeError> {
        let path = path.as_ref();
        let (_, rx, rz) = regex_captures!("^r\\.(-?[0-9]+)\\.(-?[0-9]+)\\.mca$", path.file_name().ok_or(RegionDecodeError::InvalidFileName)?.to_str().ok_or(RegionDecodeError::InvalidFileName)?).ok_or(RegionDecodeError::InvalidFileName)?;
        let coords = [rx.parse()?, rz.parse()?];
        // make sure we didn't read the region in the middle of Minecraft saving it, which can result in garbage data
        let mut buf1 = Vec::default();
        let mut err1 = match File::open(path).await {
            Ok(mut file) => match file.read_to_end(&mut buf1).await {
                Ok(_) => None,
                Err(e) => Some(e),
            },
            Err(e) => Some(e),
        };
        sleep(Duration::from_secs(1)).await;
        let mut buf2 = Vec::default();
        let mut err2 = match File::open(path).await {
            Ok(mut file) => match file.read_to_end(&mut buf2).await {
                Ok(_) => None,
                Err(e) => Some(e),
            },
            Err(e) => Some(e),
        };
        if err1.is_some() && err2.is_some() {
            return Err(err2.unwrap().into())
        }
        while err1.is_some() || err2.is_some() || buf1 != buf2 {
            mem::swap(&mut buf1, &mut buf2);
            mem::swap(&mut err1, &mut err2);
            buf2.clear();
            sleep(Duration::from_secs(1)).await;
            err2 = match File::open(path).await {
                Ok(mut file) => match file.read_to_end(&mut buf2).await {
                    Ok(_) => None,
                    Err(e) => Some(e),
                },
                Err(e) => Some(e),
            };
            if err1.is_some() && err2.is_some() {
                return Err(err2.unwrap().into())
            }
        }
        // https://minecraft.wiki/w/Region_file_format#Header
        let mut locations = [(0, 0); 1024];
        for i in 0..1024 {
            let [o0, o1, o2] = *array_ref![buf1, 4 * i, 3];
            let offset = u32::from_be_bytes([0, o0, o1, o2]);
            let sector_count = buf1[4 * i + 3];
            locations[i] = (offset, sector_count);
        }
        let mut timestamps = [DateTime::UNIX_EPOCH; 1024];
        for i in 0..1024 {
            let timestamp = *array_ref![buf1, 4096 + 4 * i, 4];
            timestamps[i] = DateTime::from_timestamp(u32::from_be_bytes(timestamp).into(), 0).expect("32-bit Unix timestamp should be in range of chrono DateTime");
        }
        Ok(Region { coords, locations, timestamps, buf: buf1 })
    }

    /// Finds the region with the given dimension and region coordinates (i.e. the block coordinates of its northwesternmost block divided by 512) in the given world folder.
    pub async fn find(world_dir: impl AsRef<Path>, dimension: Dimension, coords: [i32; 2]) -> Result<Option<Region>, RegionDecodeError> {
        let region_path = Self::path(world_dir, dimension, coords);
        Ok(if region_path.try_exists()? {
            Some(Self::open(region_path).await?)
        } else {
            None
        })
    }

    /// Returns the path where the region with the given dimension and region coordinates (i.e. the block coordinates of its northwesternmost block divided by 512) would be stored,
    /// regardless of whether that region file actually exists.
    pub fn path(world_dir: impl AsRef<Path>, dimension: Dimension, [x, z]: [i32; 2]) -> PathBuf {
        let dim_dir = match dimension {
            Dimension::Overworld => world_dir.as_ref().join("region"),
            Dimension::Nether => world_dir.as_ref().join("DIM-1").join("region"),
            Dimension::End => world_dir.as_ref().join("DIM1").join("region"),
        };
        dim_dir.join(format!("r.{x}.{z}.mca"))
    }

    /// Iterates over all regions in the given dimension of the given world folder.
    pub fn all(world_dir: impl AsRef<Path>, dimension: Dimension) -> impl Stream<Item = Result<Region, RegionDecodeError>> {
        enum State {
            Init(PathBuf),
            Continued(PathBuf, fs::ReadDir),
        }

        let dim_dir = match dimension {
            Dimension::Overworld => world_dir.as_ref().join("region"),
            Dimension::Nether => world_dir.as_ref().join("DIM-1").join("region"),
            Dimension::End => world_dir.as_ref().join("DIM1").join("region"),
        };
        let read_dir = stream::try_unfold(State::Init(dim_dir), |state| async move {
            Ok(match state {
                State::Init(dim_dir) => {
                    let mut read_dir = fs::read_dir(&dim_dir).await?;
                    read_dir.next_entry().await?.map(|entry| (entry, State::Continued(dim_dir, read_dir)))
                }
                State::Continued(path, mut read_dir) => read_dir.next_entry().await?.map(|entry| (entry, State::Continued(path, read_dir))),
            })
        });
        read_dir
            .and_then(|entry| Self::open(entry.path()))
            .filter(|res| future::ready(res.as_ref().err().is_none_or(|e| !matches!(e, RegionDecodeError::InvalidFileName)))) // ignore non-Anvil files
    }

    /// Returns a `ChunkColumn` in this region given its **absolute** chunk coordinates (i.e. the block coordinates of its northwesternmost block divided by 16).
    pub async fn chunk_column(&mut self, [x, z]: [i32; 2]) -> Result<Option<ChunkColumn>, ChunkColumnDecodeError> {
        let x_offset = x.rem_euclid(32); //TODO make sure coords are in this region
        let z_offset = z.rem_euclid(32); //TODO make sure coords are in this region
        self.chunk_column_relative([x_offset as u8, z_offset as u8]).await
    }

    /// Returns a `ChunkColumn` in this region given its chunk coordinates (i.e. the block coordinates of its northwesternmost block divided by 16) **relative** to the northwest corner of this region.
    ///
    /// # Panics
    ///
    /// Panics if either of the given coordinates is not less than 32.
    pub async fn chunk_column_relative(&mut self, [x_offset, z_offset]: [u8; 2]) -> Result<Option<ChunkColumn>, ChunkColumnDecodeError> {
        assert!(x_offset < 32 && z_offset < 32);
        let coords = [self.coords[0] * 32 + x_offset as i32, self.coords[1] * 32 + z_offset as i32];
        let (offset, sector_count) = self.locations[x_offset as usize + z_offset as usize * 32];
        if offset == 0 { return Ok(None) }
        // The Minecraft wiki says:
        // > Minecraft always pads the last chunk's data to be a multiple-of-4096B in length
        // But this seems to no longer be the case in Minecraft 1.16.1, so this implementation simply reads until EOF if the remaining file is shorter than indicated by sector_count.
        let data = self.buf.get(4096 * usize::try_from(offset).expect("offset too big for 16-bit usize")..4096 * (usize::try_from(offset).expect("offset too big for 16-bit usize") + usize::from(sector_count))).ok_or_else(|| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Range })?.to_owned();
        Ok(Some(ChunkColumn::new(coords, data)?))
    }

    /// Returns a stream over the chunk columns in this region.
    pub fn chunk_columns<'a>(&'a mut self) -> impl Stream<Item = Result<ChunkColumn, ChunkColumnDecodeError>> + use<'a> {
        stream::unfold((self, 0, 0), |(region, mut x_offset, mut z_offset)| async move {
            loop {
                if z_offset >= 32 { return None }
                let old_offsets = [x_offset, z_offset];
                x_offset += 1;
                if x_offset >= 32 {
                    z_offset += 1;
                    x_offset = 0;
                }
                match region.chunk_column_relative(old_offsets).await {
                    Ok(Some(col)) => return Some((Ok(col), (region, x_offset, z_offset))),
                    Ok(None) => {}
                    Err(e) => return Some((Err(e), (region, x_offset, z_offset))),
                }
            }
        })
    }
}

impl fmt::Debug for Region {
    /// Omits the fields containing large amounts of raw bytes, which is currently all of them.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Region")
            .field("coords", &self.coords)
            .finish_non_exhaustive()
    }
}

/// An error returned by functions that construct `ChunkColumn`s.
#[derive(Debug, thiserror::Error)]
#[error("failed to decode chunk column {}, {}: {kind}", .coords[0], .coords[1])]
pub struct ChunkColumnDecodeError {
    /// The chunk coordinates where the error occurred.
    pub coords: [i32; 2],
    /// Information about what kind of error occurred.
    #[source] pub kind: ChunkColumnDecodeErrorKind,
}

/// The contents of a `ChunkColumnDecodeError`.
#[derive(Debug, thiserror::Error)]
pub enum ChunkColumnDecodeErrorKind {
    #[allow(missing_docs)]
    #[error("{1}")]
    Io(&'static str, #[source] tokio::io::Error),
    #[allow(missing_docs)]
    #[error(transparent)] Nbt(nbt::Error),
    #[allow(missing_docs)]
    #[error("attempted to read past end of region file")]
    Range,
    /// Chunk columns are stored using different types of compression inside `.mca` files. The following compression types are currently implemented:
    ///
    /// 1. gzip
    /// 2. zlib
    ///
    /// If a chunk column with a different compression type is encountered, this error is returned, containing the compression type ID.
    #[error("unknown compression type: {0}")]
    UnknownCompressionType(u8),
}

#[derive(Deserialize)]
struct ChunkColumnInner {
    #[serde(rename = "DataVersion")]
    data_version: i32,
    #[serde(rename = "xPos")]
    x_pos: Option<i32>,
    #[serde(rename = "yPos", default)]
    y_pos: i32,
    #[serde(rename = "zPos")]
    z_pos: Option<i32>,
    #[serde(rename = "Level")]
    level: Option<ChunkLevel>,
    #[serde(default)]
    sections: Vec<ChunkSectionData>,
    #[serde(default)]
    block_entities: Vec<BlockEntity>,
    #[serde(default)]
    pub heightmaps: HashMap<String, Vec<i64>>,
}

/// The contents of the `level` field of a `ChunkColumnInner`.
#[derive(Deserialize)]
#[serde(rename_all = "PascalCase")]
struct ChunkLevel {
    /// The x chunk coordinate of this chunk, i.e. the block coordinates of its westernmost blocks divided by 16.
    #[serde(rename = "xPos")]
    x_pos: i32,
    /// The z chunk coordinate of this chunk, i.e. the block coordinates of its northernmost blocks divided by 16.
    #[serde(rename = "zPos")]
    z_pos: i32,
    /// `None` for chunks that haven't had biomes generated for them yet.
    biomes: Option<Vec<i32>>,
    sections: Vec<ChunkSectionData>,
}

impl TryFrom<ChunkColumnInner> for ChunkColumn {
    type Error = &'static str;

    fn try_from(ChunkColumnInner { data_version, x_pos, y_pos, z_pos, level, sections, block_entities, heightmaps }: ChunkColumnInner) -> Result<Self, &'static str> {
        let heightmaps = heightmaps.into_iter()
            .map(|(name, heightmap)| (name, (0..16).map(|z| (0..16).map(|x| {
                let block_index = 16 * z + x;
                let bits_per_index = 9;
                let indexes_per_long = 64 / bits_per_index as usize;
                let containing_long = block_index / indexes_per_long;
                let index_offset = block_index % indexes_per_long;
                let bit_offset = index_offset * bits_per_index as usize;
                let mask = 2i32.pow(bits_per_index) - 1;
                let distance_from_bottom = (heightmap[containing_long] >> bit_offset) as i32 & mask;
                distance_from_bottom + 16 * y_pos
            }).collect_vec().try_into().unwrap()).collect_vec().try_into().unwrap()))
            .collect();
        Ok(if let Some(ChunkLevel { x_pos, z_pos, biomes, sections }) = level {
            Self {
                sections: sections.into_iter().map(|data| ChunkSection { data_version, data }).collect(),
                x_pos, y_pos, z_pos, biomes, block_entities, heightmaps,
            }
        } else {
            Self {
                x_pos: x_pos.ok_or("missing xPos field")?,
                z_pos: z_pos.ok_or("missing zPos field")?,
                biomes: None, //TODO
                sections: sections.into_iter().map(|data| ChunkSection { data_version, data }).collect(),
                y_pos, block_entities, heightmaps,
            }
        })
    }
}

/// A chunk column represents 16 chunks stacked vertically, or 16×256×16 blocks.
#[derive(Deserialize)]
#[serde(try_from = "ChunkColumnInner")]
pub struct ChunkColumn {
    /// The x chunk coordinate of this chunk, i.e. the block coordinates of its westernmost blocks divided by 16.
    pub x_pos: i32,
    /// The minimum y chunk coordinate of this chunk, i.e. the block coordinates of its lowest blocks divided by 16.
    pub y_pos: i32,
    /// The z chunk coordinate of this chunk, i.e. the block coordinates of its northernmost blocks divided by 16.
    pub z_pos: i32,
    /// `None` for chunks that haven't had biomes generated for them yet.
    biomes: Option<Vec<i32>>,
    /// The vertical 16x16x16 sections, or “chunks”, of this chunk column.
    pub sections: Vec<ChunkSection>,
    /// The [block entities](https://minecraft.wiki/w/Block_entity) in this chunk column.
    pub block_entities: Vec<BlockEntity>,
    /// The [heightmaps](https://minecraft.wiki/w/Heightmap) for this chunk column.
    pub heightmaps: HashMap<String, [[i32; 16]; 16]>,
}

impl ChunkColumn {
    fn new(coords: [i32; 2], data: Vec<u8>) -> Result<ChunkColumn, ChunkColumnDecodeError> {
        // https://minecraft.wiki/w/Region_file_format#Payload
        let mut data_cursor = &*data;
        let mut len = [0; 4];
        std::io::Read::read_exact(&mut data_cursor, &mut len).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("read compressed length", e) })?;
        let len = u32::from_be_bytes(len) - 1;
        let mut compression = [0; 1];
        std::io::Read::read_exact(&mut data_cursor, &mut compression).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Io("read compression type", e) })?;
        Ok(match compression {
            [1] => nbt::from_gzip_reader(std::io::Read::take(data_cursor, len as u64)).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Nbt(e) })?,
            [2] => nbt::from_zlib_reader(std::io::Read::take(data_cursor, len as u64)).map_err(|e| ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::Nbt(e) })?,
            [compression] => return Err(ChunkColumnDecodeError { coords, kind: ChunkColumnDecodeErrorKind::UnknownCompressionType(compression) }),
        })
    }

    fn coords_to_relative(&self, [x, y, z]: [i32; 3]) -> Result<[u8; 3], [i32; 3]> {
        if x >= self.x_pos << 4 && x < (self.x_pos + 1) << 4 && y >= 0 && y < 256 && z >= self.z_pos << 4 && z < (self.z_pos + 1) << 4 {
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
        let biomes = if let Some(ref biomes) = self.biomes {
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
        let biomes = if let Some(ref biomes) = self.biomes {
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

    /// Returns the [`ChunkSection`] with the given chunk y coordinate.
    pub fn section_at(&self, y: i8) -> Option<&ChunkSection> {
        self.sections.iter().find(|section| section.data.y == y)
    }

    /// Returns the [`ChunkSection`] with the given chunk y coordinate.
    pub fn into_section_at(self, y: i8) -> Option<ChunkSection> {
        self.sections.into_iter().find(|section| section.data.y == y)
    }
}

/// A 16x16x16 chunk.
pub struct ChunkSection {
    data_version: i32,
    data: ChunkSectionData,
}

#[derive(Deserialize)]
struct ChunkSectionData {
    #[serde(rename = "Y")]
    y: i8,
    #[serde(default)]
    block_states: BlockStates,
}

#[derive(Default, Deserialize)]
struct BlockStates {
    palette: Vec<BlockState>,
    data: Option<Vec<i64>>,
}

impl ChunkSection {
    /// The y chunk coordinate of this chunk, i.e. the block coordinates of its lowest blocks divided by 16.
    pub fn y(&self) -> i8 { self.data.y }

    /// Returns a `BlockState` in this chunk given its **absolute** coordinates.
    ///
    /// # Panics
    ///
    /// If the data is in an invalid format.
    pub fn block(&self, [x, y, z]: [i32; 3]) -> Cow<'_, BlockState> {
        let x_offset = x.rem_euclid(16); //TODO make sure coords are in this chunk
        let y_offset = y.rem_euclid(16); //TODO make sure coords are in this chunk
        let z_offset = z.rem_euclid(16); //TODO make sure coords are in this chunk
        self.block_relative([x_offset as u8, y_offset as u8, z_offset as u8])
    }

    /// Returns a `BlockState` in this chunk given its coordinates **relative** to the bottom northwest corner of this chunk.
    ///
    /// # Panics
    ///
    /// Panics if any of the given coordinates is not less than 16 or if the data is in an invalid format.
    pub fn block_relative(&self, [x, y, z]: [u8; 3]) -> Cow<'_, BlockState> {
        assert!(x < 16 && y < 16 && z < 16);
        match &*self.data.block_states.palette {
            [] => Cow::Owned(BlockState::default()),
            [palette_entry] => Cow::Borrowed(palette_entry),
            palette => {
                let data = self.data.block_states.data.as_ref().expect("no block state data with a palette size ≠ 1");
                let block_index = 256 * y as usize + 16 * z as usize + x as usize;
                let bits_per_index = 4.max(usize::BITS - (palette.len() - 1).leading_zeros());
                let index = if self.data_version >= 2529 { // starting in 20w17a, indices are no longer split across multiple longs
                    let indexes_per_long = 64 / bits_per_index as usize;
                    let containing_long = block_index / indexes_per_long;
                    let index_offset = block_index % indexes_per_long;
                    let bit_offset = index_offset * bits_per_index as usize;
                    let mask = 2usize.pow(bits_per_index) - 1;
                    (data[containing_long] >> bit_offset) as usize & mask
                } else {
                    let bit_index = block_index * bits_per_index as usize;
                    let containing_index = bit_index / 64;
                    let offset = bit_index % 64;
                    let bit_end_index = bit_index + bits_per_index as usize;
                    let containing_end_index = bit_end_index / 64;
                    let source_fields = containing_end_index - containing_index;
                    let mask = 2usize.pow(bits_per_index) - 1;
                    let mut index = 0;
                    for ii in 0..=source_fields {
                        let state_index = containing_index + ii;
                        let field = data[state_index] % 2i64.pow(64);
                        let part = field << (64 * ii);
                        index |= part;
                    }
                    (index >> offset) as usize & mask
                };
                Cow::Borrowed(&palette[index])
            }
        }
    }

    /// # Performance
    ///
    /// This function simply iterates over all block coordinates in this chunk and calls [`Self::block_relative`] for each of them.
    /// Additionally, creating the arrays has significant performance overhead.
    /// Therefore, when writing performance-sensitive code, you should consider calling `block_relative` directly instead.
    ///
    /// # Panics
    ///
    /// If the data is in an invalid format.
    pub fn blocks(&self) -> [[[Cow<'_, BlockState>; 16]; 16]; 16] {
        array::from_fn(|y| array::from_fn(|z| array::from_fn(|x| self.block_relative([x as u8, y as u8, z as u8]))))
    }
}

/// A block.
#[serde_as]
#[derive(Debug, Default, Clone, PartialEq, Eq, Deserialize)]
#[cfg_attr(feature = "async-proto", derive(Protocol))]
#[serde(rename_all = "PascalCase")]
pub struct BlockState {
    /// The [resource location](https://minecraft.wiki/w/Resource_location) of the block.
    #[serde_as(as = "DisplayFromStr")]
    pub name: BlockId,
    /// The [block state](https://minecraft.wiki/w/Block_states) properties of the block.
    #[serde(default)]
    pub properties: HashMap<String, String>,
}

/// A [block entity](https://minecraft.wiki/w/Block_entity).
#[derive(Deserialize)]
pub struct BlockEntity {
    /// The [resource location](https://minecraft.wiki/w/Resource_location) of the block entity.
    pub id: String,
    /// The X coordinate of the block.
    pub x: i32,
    /// The Y coordinate of the block.
    pub y: i32,
    /// The Z coordinate of the block.
    pub z: i32,
    /// Data specific to the block type.
    #[serde(flatten)]
    pub rest: nbt::Map<String, nbt::Value>,
}

#[tokio::test]
async fn test_weird_region() {
    Region::open("assets\\r.11.-5.mca").await.unwrap().chunk_column([372, -132]).await.unwrap();
}
