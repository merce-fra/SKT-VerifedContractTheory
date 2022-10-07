{ pkgs ? import <nixpkgs> {} }:
let coqPackages = pkgs.coqPackages_8_9 ; in
pkgs.mkShell {
  buildInputs = [
  coqPackages.coq
  coqPackages.coquelicot
  ];
}
