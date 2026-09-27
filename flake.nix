{
    inputs.flake.url = "github:fenhl/flake";
    outputs = attrs: attrs.flake.lib {};
}
