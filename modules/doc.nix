# deduxit © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# The library's documentation: `rocq doc' over the theories, through the
# `html' target of the makefile `rocq makefile' generates, which compiles
# the library first for the cross-references. `index.html' is the list of
# modules; the release's Pages site serves the directory as it is.
{ ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      inherit (pkgs) lib;
      inherit (pkgs.rocqPackages) rocq-core stdlib;
      library = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [
          ../_RocqProject
          ../Makefile
          ../theories
        ];
      };
    in
    {
      packages.doc =
        pkgs.runCommand "rocq-deduxit-doc"
          {
            nativeBuildInputs = [
              rocq-core
              stdlib
            ];
            ROCQPATH = "${stdlib}/lib/coq/${rocq-core.rocq-version}/user-contrib";
          }
          ''
            export HOME=$TMPDIR
            cp -r ${library}/. source
            chmod -R u+w source
            make -C source -j"$NIX_BUILD_CORES" html
            mkdir -p $out/share/doc
            cp -r source/html $out/share/doc/rocq-deduxit
          '';
    };
}
