# linlog © Fabian Lukas Grubmüller 2026
# Licensed under the EUPL

# The platforms deduxit's own flake declares. CI builds and checks
# x86_64-linux alone; the others evaluate and are not built anywhere.
{
  systems = [
    "x86_64-linux"
    "aarch64-linux"
    "aarch64-darwin"
  ];
}
