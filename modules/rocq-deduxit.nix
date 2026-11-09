# deduxit © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# The library (logical root `Deduxit', today's calculus under
# `Deduxit.Linear'): the package `rocq-deduxit', built as
# nixpkgs builds a Rocq library (mkRocqDerivation over the library's own
# Makefile, the reference manual's wrapper of `rocq makefile' on
# _RocqProject), and the check `rocq-deduxit', which compiles every
# certificate under tests/ (logical path `Deduxit.Linear.Tests') against
# the installed library and requires
# `Print Assumptions' of the soundness theorems to answer `Closed under the
# global context'. Rocq prints nothing for a file it accepts, so any other
# output fails the check, as does an `Admitted', `admit', `Axiom',
# `Parameter' or `Conjecture' in a source. Rocq and its standard library
# are nixpkgs'.
{ ... }:
{
  perSystem =
    { config, pkgs, ... }:
    let
      inherit (pkgs) lib;

      # The library's version is the opam file's.
      version = builtins.head (
        builtins.match ''.*version: "([0-9.]+)".*'' (builtins.readFile ../rocq-deduxit.opam)
      );

      # Every Rocq the opam file's bounds admit, by nixpkgs' package set of
      # each minor version; `rocqPackages' is one of them, the default.
      admitted = {
        "9_0" = pkgs.rocqPackages_9_0;
        "9_1" = pkgs.rocqPackages_9_1;
        "9_2" = pkgs.rocqPackages_9_2;
        "9_3" = pkgs.rocqPackages_9_3;
      };

      library = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [
          ../_RocqProject
          ../Makefile
          ../theories
        ];
      };

      tests = lib.fileset.toSource {
        root = ../tests;
        fileset = lib.fileset.fileFilter (file: file.hasExt "v") ../tests;
      };

      # The library built with one Rocq, as nixpkgs builds a Rocq library.
      packageFor =
        rocqPackages:
        rocqPackages.mkRocqDerivation {
          pname = "deduxit";
          opam-name = "rocq-deduxit";
          inherit version;
          # A release whose source is this tree: `hash' must be present, and
          # the empty string stands for the fake hash nothing fetches.
          release.${version} = {
            src = library;
            hash = "";
          };
          propagatedBuildInputs = [ rocqPackages.stdlib ];
          meta = {
            description = "The Rocq library of deduxit: linear logic, proof terms, their checker and its soundness";
            homepage = "https://github.com/deduxit/rocq-deduxit";
            license = lib.licenses.eupl12;
          };
        };

      # The certificates under tests/ compiled against that build, and the
      # theorems' assumptions closed.
      checkFor =
        rocqPackages:
        let
          rocq = rocqPackages.rocq-core;
          inherit (rocqPackages) stdlib;
          package = packageFor rocqPackages;
          userContrib = "lib/coq/${rocq.rocq-version}/user-contrib";
        in
        pkgs.runCommand "check-rocq-deduxit-${rocq.rocq-version}"
          {
            nativeBuildInputs = [
              rocq
              stdlib
              package
            ];
            ROCQPATH = "${stdlib}/${userContrib}:${package}/${userContrib}";
          }
          ''
            export HOME=$TMPDIR
            if grep -rnE '^[[:space:]]*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted)\b|\badmit\.' \
                ${library}/theories ${tests}; then
              echo "an assumption or an admitted proof in the library"
              exit 1
            fi
            cp ${tests}/*.v .
            for file in *.v; do
              [ "$file" = Assumptions.v ] && continue
              rocq compile -Q . Deduxit.Linear.Tests "$file" 2>&1 | tee log
              if [ -s log ]; then exit 1; fi
            done
            rocq compile -Q . Deduxit.Linear.Tests Assumptions.v >assumptions 2>&1 || { cat assumptions; exit 1; }
            cat assumptions
            # One line per theorem the file asks about, and nothing else.
            theorems=$(grep -c '^Print Assumptions' Assumptions.v)
            for _ in $(seq "$theorems"); do echo 'Closed under the global context'; done |
              diff - assumptions
            touch $out
          '';
    in
    {
      packages = {
        rocq-deduxit = packageFor pkgs.rocqPackages;
        default = config.packages.rocq-deduxit;
      };

      # `rocq-deduxit' with the default Rocq (deduxit's flake re-exports
      # it), and `rocq-deduxit-9_N' with each other one the bounds admit.
      checks = {
        rocq-deduxit = checkFor pkgs.rocqPackages;
      }
      //
        lib.mapAttrs'
          (minor: rocqPackages: lib.nameValuePair "rocq-deduxit-${minor}" (checkFor rocqPackages))
          (
            lib.filterAttrs (
              _: rocqPackages: rocqPackages.rocq-core.version != pkgs.rocqPackages.rocq-core.version
            ) admitted
          );

      # `make' in the repository builds the library with this Rocq.
      devShells.default =
        let
          inherit (pkgs.rocqPackages) rocq-core stdlib;
        in
        pkgs.mkShell {
          packages = [
            rocq-core
            stdlib
          ];
          ROCQPATH = "${stdlib}/lib/coq/${rocq-core.rocq-version}/user-contrib";
        };
    };
}
