# deduxit © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# The library's documentation: `rocq doc' over the theories, through the
# `html' target of the makefile `rocq makefile' generates, which compiles
# the library first for the cross-references. `index.html' is the list of
# modules; the release's Pages site serves the directory as it is. Up to
# 0.2.0 the modules were `Linlog.X', so each page `Deduxit.Linear.X.html'
# has a page `Linlog.X.html' beside it that forwards there, the fragment
# kept, for the old deep links.
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
            cd $out/share/doc/rocq-deduxit
            for page in Deduxit.Linear.*.html; do
              target=$page
              name=''${page#Deduxit.Linear.}
              name=''${name%.html}
              cat >"Linlog.$name.html" <<EOF
            <!DOCTYPE html>
            <html lang="en">
            <head>
            <meta charset="utf-8">
            <title>Deduxit.Linear.$name</title>
            <link rel="canonical" href="$target">
            <meta http-equiv="refresh" content="0; url=$target">
            <script>location.replace("$target" + location.hash);</script>
            </head>
            <body>
            <p>The module Linlog.$name is now <a href="$target">Deduxit.Linear.$name</a>.</p>
            </body>
            </html>
            EOF
            done
          '';
    };
}
