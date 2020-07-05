{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs-channels/archive/0a9d9946ed3e1ec526848db2f77f2dc978b46bb5.tar.gz";
  sha256 = "1gdqnb5g5h47gqx95lyzlqnmhzkcnh27gia778cr79cmgvwasb69";
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
