{withEmacs ? false,
 nixpkgs ? (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/4aa5466cbc741097218a1c494a7b832a17d1967d.tar.gz),
 coq-version ? "8.12",
 print-env ? false
}:
with import nixpkgs {
  overlays = [ (super: self: {
    coqPackages = { "8.12" = super.coqPackages_8_12;  }."${coq-version}".overrideScope' (self: super: {
      coq = super.coq.override {
        ocamlPackages = super.coq.ocamlPackages.overrideScope' (self: super: {
          elpi = super.elpi.overrideAttrs (old: {
            name = "elpi-1.12.0";
            src = fetchTarball https://github.com/LPCIC/elpi/archive/v1.12.0.tar.gz;
          });
        });
      };
      # Coq package override example:
      coq-elpi = super.coq-elpi.overrideAttrs (old: {
        name = "coq8.12-elpi-1.8.0";
        src = fetchTarball https://github.com/LPCIC/coq-elpi/archive/v1.8.0.tar.gz;
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
