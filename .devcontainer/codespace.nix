let
  pkgs = (import ../pin.nix {}).pkgs;
in pkgs.mkShell {
  packages = with pkgs; [
    coqPackages.coq
    coqPackages.coq-lsp
    coqPackages.ssprove
  ];
}
