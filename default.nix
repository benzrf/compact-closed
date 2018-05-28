{ mkDerivation, base, constraints, containers, finite-typelits
, linear, mtl, semigroupoids, stdenv, template-haskell
}:
mkDerivation {
  pname = "compact-closed";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base constraints containers finite-typelits linear mtl
    semigroupoids template-haskell
  ];
  license = stdenv.lib.licenses.gpl3;
}
