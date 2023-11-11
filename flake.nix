{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = inputs:
    inputs.flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = inputs.nixpkgs.legacyPackages.${system};

          devShells.default = pkgs.mkShell {
            buildInputs = [
              pkgs.coq
              pkgs.coqPackages.stdpp
              pkgs.coqPackages.coqide
            ];
          };
        in
        {
          inherit devShells;
        });
}

