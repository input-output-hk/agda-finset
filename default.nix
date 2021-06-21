{ nixpkgs ?  <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "0.9";
  pname = "finset";
  src = ./src;
  everythingFile = "README.agda";
  buildInputs = [
    agdaPackages.standard-library
  ];
}
