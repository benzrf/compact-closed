{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, constraints, containers
      , finite-typelits, linear, mtl, semigroupoids, stdenv
      , template-haskell
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
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
