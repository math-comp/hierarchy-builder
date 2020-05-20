{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/CohenCyril/nixpkgs/archive/8d04d29adb547353ed9fb5c5c4aa6d540e198366.tar.gz";
  sha256 = "1v4l37xkadpnkydpycnk9hrjgh6yc792k66yi7f6203zzr0phzx8";
}),
 coq-version ? "8.11",
 print-env ? false
}:
with import nixpkgs {
  overlays = [ (super: self: {
    coqPackages = { "8.11" = super.coqPackages_8_11;  }."${coq-version}".overrideScope' (self: super: {
      ## Coq package override example:
      # coq-elpi = super.coq-elpi.overrideAttrs (old: {
      #   name = "coq8.11-elpi-v1.4.0";
      #   src = fetchTarball https://github.com/LPCIC/coq-elpi/archive/v1.4.0.tar.gz;
    });
    coq = self.coqPackages.coq;
  })];
};
let pgEmacs = emacsWithPackages (epkgs: with epkgs.melpaStablePackages; [proof-general]); in
coqPackages.hierarchy-builder.overrideAttrs (old: {
  name = "coq${coq.coq-version}-hierarchy-builder-dev";
  src = ./.;
  buildInputs = old.buildInputs ++
                (if lib.trivial.inNixShell then lib.optional withEmacs pgEmacs
                 else []);
}
// (if lib.trivial.inNixShell then {
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
} else {}))
