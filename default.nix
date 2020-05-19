{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/CohenCyril/nixpkgs/archive/7f59c094a0e5c8659856e611075fe88d6177830f.tar.gz";
  sha256 = "00cf4r8dqfx2hwlwaqb239h72m4s0wl97i98424xd4hki0vzifbi";
}),
 coq-version ? "8.11",
 print-env ? false
}:
with import nixpkgs {};
let
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
  myCoqPackages = {
    "8.10" = coqPackages_8_10;
    "8.11" = coqPackages_8_11;
    }."${coq-version}";
  coq = myCoqPackages.coq;
  coq-elpi = myCoqPackages.coq-elpi.overrideAttrs(o: {
    name = "coq8.11-elpi-v1.4.0";
    src = fetchTarball https://github.com/LPCIC/coq-elpi/archive/v1.4.0.tar.gz;
  });
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
