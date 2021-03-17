{ mathcomp, coq, coq-elpi, hierarchy-builder-shim,
  mathcomp-single-planB-src }:
(mathcomp.override {single = true;}).overrideAttrs (old: {
  src = mathcomp-single-planB-src;
  name = "coq${coq.coq-version}-mathcomp-planB";
  buildPhase = ''
    make -j$NIX_BUILD_CORES -C mathcomp only \
      TGTS="fingroup/presentation.vo algebra/ssralg.vo ssreflect/order.vo"
  '';
  propagatedBuildInputs = old.propagatedBuildInputs ++
                          [ coq-elpi hierarchy-builder-shim ];
  installPhase = "echo NO INSTALL";
})
