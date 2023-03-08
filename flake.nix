{
  inputs = { nixpkgs.url = "github:nixos/nixpkgs"; };

  outputs = { self, nixpkgs }:
    let pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in with pkgs; {
      devShell.x86_64-linux = pkgs.mkShell {
        buildInputs = [
          coq
          coqPackages.mathcomp
        ];
      };
   };
}
