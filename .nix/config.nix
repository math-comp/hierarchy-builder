{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.14";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "hierarchy-builder";
      mathcomp.job = true;
      mathcomp-single.job = true;
      hierarchy-builder-shim.job = true;
      mathcomp-single-planB-src.job = true;
      mathcomp-single-planB.job = true;
      graph-theory.job = false;
    };
  in {
    "coq-mcHB-8.14".coqPackages = {
      coq.override.version = "8.14";
    } // mcHBcommon;
    "coq-mcHB-8.13".coqPackages = {
      coq.override.version = "8.13";
    } // mcHBcommon;
    "coq-8.14".coqPackages = {
      coq.override.version = "8.14";
    };
    "coq-8.13".coqPackages = {
      coq.override.version = "8.13";
    };
  };
}
