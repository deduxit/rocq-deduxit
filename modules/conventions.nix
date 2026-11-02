# linlog © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# The repository's conventions as checks, so that they never regress:
# `conventions' (every source file starts with the licence header, and no
# comment names the plan of linlog's sessions that organised the work),
# `typos' (spelling, configured by typos.toml), `deadnix' and `actionlint'
# (the workflows, which no local run exercises otherwise; nixpkgs'
# actionlint runs shellcheck on their `run' scripts).
{ lib, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      tree = lib.fileset.toSource {
        root = ../.;
        fileset = ../.;
      };
    in
    {
      checks = {
        conventions = pkgs.runCommand "check-conventions" { nativeBuildInputs = [ pkgs.ripgrep ]; } ''
          cd ${tree}
          status=0
          sources=$(rg --files --hidden --glob '!.git' --glob '!.jj' \
            --glob '*.v' --glob '*.nix' --glob '*.toml' --glob '*.sh' \
            --glob '*.py' --glob '*.yml' --glob '*.yaml' --glob 'Makefile' \
            --glob '*.opam' --glob '.envrc')
          for file in $sources; do
            # A script's header follows its shebang line.
            if ! head -n 3 "$file" | rg --quiet --fixed-strings 'linlog © Fabian Lukas Grubmüller 2026' \
              || ! head -n 4 "$file" | rg --quiet --fixed-strings 'Licensed under the EUPL'; then
              echo "$file: no licence header"
              status=1
            fi
          done
          # A comment says what the code does or why, in terms of the
          # repository: never a step, a decision number or a file of the
          # plan that organised the work. `.claude/' is the setup of the
          # sessions themselves.
          plan='plan/|\b[Ss]teps? [0-9]+\b|\bD[0-9]{1,2}a?\b|conduct\.md'
          if rg --line-number --hidden --glob '!.claude/**' --glob '!.git' --glob '!.jj' \
            --glob '*.v' --glob '*.nix' --glob '*.toml' --glob '*.sh' \
            --glob '*.py' --glob '*.yml' --glob '*.yaml' --glob 'Makefile' \
            "(#|\(\*).*($plan)" .; then
            echo "a comment names the plan"
            status=1
          fi
          if rg --line-number 'plan/|\b[Ss]teps? [0-9]+\b' README.md; then
            echo "README names the plan"
            status=1
          fi
          [ "$status" = 0 ] && touch $out
          exit "$status"
        '';

        typos = pkgs.runCommand "check-typos" { nativeBuildInputs = [ pkgs.typos ]; } ''
          cd ${tree}
          typos --config typos.toml .
          touch $out
        '';

        deadnix = pkgs.runCommand "check-deadnix" { nativeBuildInputs = [ pkgs.deadnix ]; } ''
          cd ${tree}
          deadnix --fail .
          touch $out
        '';

        actionlint = pkgs.runCommand "check-actionlint" { nativeBuildInputs = [ pkgs.actionlint ]; } ''
          cd ${tree}
          actionlint .github/workflows/*
          touch $out
        '';
      };
    };
}
