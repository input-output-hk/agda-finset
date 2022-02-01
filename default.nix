{ nixpkgs ? <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "0.9";
  pname = "finset";
  src = ./.;
  everythingFile = "src/README.agda";
  buildInputs = [
    agdaPackages.standard-library
  ];
}
