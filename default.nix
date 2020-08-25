{withEmacs ? false,
 nixpkgs ? (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/e97fdce4e1b945c9ec30d4d90a451f1577f5cf4a.tar.gz),
 coq-version ? "8.11",
 print-env ? false
}:
with import nixpkgs {
  overlays = [ (super: self: {
    coqPackages = { "8.11" = super.coqPackages_8_11;  }."${coq-version}".overrideScope' (self: super: {
      # Coq package override example:
      coq-elpi = super.coq-elpi.overrideAttrs (old: {
        name = "coq8.11-elpi-1.5.0";
        src = fetchTarball https://github.com/LPCIC/coq-elpi/archive/v1.5.0.tar.gz;
      });
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
      for x in $buildInputs $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
} else {}))
