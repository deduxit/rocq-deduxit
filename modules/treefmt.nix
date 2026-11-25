# deduxit © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# `nix fmt' and the `treefmt' check. Rocq sources have no formatter;
# Markdown and .claude/settings.json (which Claude Code rewrites itself)
# are left alone.
{ inputs, ... }:
{
  imports = [ inputs.treefmt-nix.flakeModule ];

  perSystem = {
    treefmt = {
      programs = {
        nixfmt.enable = true;
        # typos.toml
        taplo.enable = true;
        # The scripts' style, two spaces and `-s'; treefmt-nix's defaults
        # are tabs and no `-s'.
        shfmt = {
          enable = true;
          indent_size = 2;
          simplify = true;
        };
        shellcheck.enable = true;
        # The Claude Code hooks.
        ruff-format.enable = true;
      };

      # treefmt walks the whole directory outside a VCS work tree.
      settings.global.excludes = [
        ".direnv/**"
        "result*"
      ];
    };
  };
}
