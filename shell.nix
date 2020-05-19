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
  coq-elpi = myCoqPackages.coq-elpi.overrideAttrs (o: {
    name = "coq8.11-elpi-784659c";
    src = fetchTarball https://github.com/LPCIC/coq-elpi/archive/784659cbc4ced031b87fc9eda349162169f15084.tar.gz;
  });
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq coq.ocaml coq.ocamlPackages.elpi coq-elpi ]
                ++ lib.optional withEmacs pgEmacs
                ++ [ pythonPackages.pygments ] ;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}
