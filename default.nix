{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/82b54d490663b6d87b7b34b9cfc0985df8b49c7d.tar.gz";
  sha256 = "12gpsif48g5b4ys45x36g4vdf0srgal4c96351m7gd2jsgvdllyf";
}),
 coq-version ? "8.10",
 print-env ? false
}:
with import nixpkgs {};
let
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
  myCoqPackages = {
    "8.7" = coqPackages_8_7;
    "8.8" = coqPackages_8_8;
    "8.9" = coqPackages_8_9;
    "8.10" = coqPackages_8_10;
    }."${coq-version}";
  coq = myCoqPackages.coq;
  coq-elpi =  myCoqPackages.coq-elpi;
in
stdenv.mkDerivation {
  name = "coq${coq.coq-version}-hierarchy-builder-dev";

  src = ./.;

  nativeBuildInputs = [ which ];
  buildInputs = [ coq coq.ocaml coq.ocamlPackages.elpi coq-elpi ];

  installPhase = ''make -f Makefile.coq VFILES=structures.v COQLIB=$out/lib/coq/${coq.coq-version}/ install'';

  meta = {
    description = "Coq plugin embedding ELPI.";
    maintainers = [ stdenv.lib.maintainers.cohencyril ];
    license = stdenv.lib.licenses.lgpl21;
    inherit (coq.meta) platforms;
    inherit (src.meta) homepage;
  };

  passthru = {
    compatibleCoqVersions = stdenv.lib.flip builtins.hasAttr params;
  };
}
