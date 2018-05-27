{ mkDerivation, base, constraints, finite-typelits, linear, stdenv
}:
mkDerivation {
  pname = "compact-closed";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base constraints finite-typelits linear
  ];
  license = stdenv.lib.licenses.gpl3;
}
