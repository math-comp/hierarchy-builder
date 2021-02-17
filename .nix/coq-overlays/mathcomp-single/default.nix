{ mathcomp, coq-elpi, hierarchy-builder, version ? null }:
(mathcomp.override {single = true;}).overrideAttrs (old: {
  buildPhase = "make -j $(max_jobs) -C mathcomp ./algebra/ssralg.vo";
  propagatedBuildInputs = old.propagatedBuildInputs ++
                          [ coq-elpi hierarchy-builder ];
  installPhase = "echo NO INSTALL";
})
