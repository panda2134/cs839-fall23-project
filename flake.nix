{
  inputs = {
    nix-vscode-extensions.url = "github:nix-community/nix-vscode-extensions";
    vscoq.url = "github:coq-community/vscoq";
    flake-utils.follows = "nix-vscode-extensions/flake-utils";
    nixpkgs.follows = "nix-vscode-extensions/nixpkgs";
  };

  outputs = inputs:
    inputs.flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = inputs.nixpkgs.legacyPackages.${system};
          extensions = inputs.nix-vscode-extensions.extensions.${system};
          inherit (pkgs) vscode-with-extensions vscodium;

          packages.default =
            vscode-with-extensions.override {
              vscode = vscodium;
              vscodeExtensions = [
                extensions.vscode-marketplace.maximedenes.vscoq
              ];
            };

          devShells.default = pkgs.mkShell {
            buildInputs = [
              packages.default
              pkgs.coq
              inputs.vscoq.packages.${system}.vscoq-language-server
            ];
            shellHook = ''
              printf "VSCodium with extensions:\n"
              codium --list-extensions
            '';
          };
        in
        {
          inherit packages devShells;
        });
}

