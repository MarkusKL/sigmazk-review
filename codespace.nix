let
  args = { bundle = "9.1"; inNixShell = true; };
  nixpkgs = import ./default.nix args;
  pkgs = nixpkgs.pkgs;
in pkgs.mkShell {
  packages = with pkgs; [
    coqPackages.coq
    coqPackages.coq-lsp
    coqPackages.ssprove
  ];
}
