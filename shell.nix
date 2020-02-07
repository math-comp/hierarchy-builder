{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/CohenCyril/nixpkgs/archive/e731156350702dc9c4ebda66674f70cca773421c.tar.gz";
  sha256 = "0vzzmyyrc7rvw80b3rckwcm56536wjiysmghpdnjcr6g5d5b9c7x";
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
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq myCoqPackages.coq-elpi ]
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
