{
  inputs = {
    nix-vscode-extensions.url = "github:nix-community/nix-vscode-extensions";
    vscoq.url = "github:coq-community/vscoq";
    flake-utils.follows = "nix-vscode-extensions/flake-utils";
    nixpkgs.follows = "nix-vscode-extensions/nixpkgs";
    coq-8_18 = {
      type = "github";
      owner = "coq";
      repo = "coq";
      ref = "V8.18.0";
    };

    coq-8_18.inputs.nixpkgs.follows = "nixpkgs";
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
              inputs.coq-8_18.defaultPackage.${system}
              inputs.vscoq.packages.${system}.vscoq-language-server
              (inputs.nixpkgs.legacyPackages.${system}.coqPackages.callPackage ./stdpp.nix {})
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

