# deduxit © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# A shell for opam (`nix develop .#opam'): what `scripts/opam-install.sh'
# needs to install the package from its opam file into fresh switches, one
# per Rocq version the bounds admit, as a user of opam would. OCaml 4.14
# is the switches' compiler (`ocaml-system'): every admitted rocq-runtime
# accepts it, and the Rocq opam repository's CI builds with it, while
# rocq-runtime 9.0 refuses nixpkgs' default OCaml 5.5. gmp is zarith's,
# which rocq-runtime needs. The switches are built from the network, so
# none of this runs in a check.
{ ... }:
{
  perSystem =
    { pkgs, ... }:
    {
      devShells.opam = pkgs.mkShell {
        packages = [
          pkgs.opam
          pkgs.ocaml-ng.ocamlPackages_4_14.ocaml
          pkgs.gmp
          pkgs.pkg-config
          pkgs.gnumake
          pkgs.git
          pkgs.curl
          pkgs.unzip
          pkgs.rsync
          pkgs.which
        ];
      };
    };
}
