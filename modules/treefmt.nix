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
        shfmt.enable = true;
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
