#!/usr/bin/env bash
# linlog © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# Installs the package from the repository's opam file into a fresh opam
# switch for each Rocq version given, as a user of opam would, and
# compiles a file that imports every module of the library; `opam lint'
# first. Run it in the flake's opam shell, with the network:
#
#   nix develop .#opam -c scripts/opam-install.sh 9.0.1 9.1.1 9.2.0 9.3.0
#
# Every switch lives in a temporary opam root, which is removed at the
# end; OPAM_INSTALL_ROOT keeps it instead. The tree is copied as it is
# (`--kind path'), so uncommitted changes are what is installed.
set -euo pipefail

if [ "$#" = 0 ]; then
  echo "usage: scripts/opam-install.sh ROCQ_VERSION…" >&2
  exit 2
fi

repo=$(cd "$(dirname "$0")/.." && pwd)
if [ -n "${OPAM_INSTALL_ROOT:-}" ]; then
  root=$OPAM_INSTALL_ROOT
  mkdir -p "$root"
else
  root=$(mktemp -d)
  trap 'rm -rf "$root"' EXIT
fi
export OPAMROOT="$root/opam" OPAMYES=1 OPAMCOLOR=never
jobs=${OPAM_JOBS:-4}

opam lint "$repo/rocq-linlog.opam"

opam init --bare --no-setup --disable-sandboxing \
  default https://opam.ocaml.org
opam repository add --dont-select rocq-released https://rocq-prover.org/opam/released
# The system packages a build needs (gmp, the C compiler) come from the
# shell, not from a system package manager opam would call.
opam option --global depext=false

modules=$(sed -n 's|^theories/\(.*\)\.v$|\1|p' "$repo/_RocqProject" | tr '\n' ' ')

for version in "$@"; do
  switch="rocq-$version"
  echo "== Rocq $version"
  opam switch create "$switch" --repositories=default,rocq-released \
    --packages=ocaml-system --jobs="$jobs"
  opam install --switch="$switch" --jobs="$jobs" "rocq-core.$version" rocq-stdlib
  opam pin add --switch="$switch" --kind=path --no-action rocq-linlog "$repo"
  opam install --switch="$switch" --jobs="$jobs" rocq-linlog
  opam list --switch="$switch" --installed --columns=name,version \
    rocq-core rocq-stdlib rocq-linlog
  work=$(mktemp -d)
  echo "From Linlog Require $modules." >"$work/Everything.v"
  (cd "$work" && opam exec --switch="$switch" -- rocq compile Everything.v)
  rm -rf "$work"
  opam remove --switch="$switch" rocq-linlog
  echo "== Rocq $version: installed, imported and removed"
done
