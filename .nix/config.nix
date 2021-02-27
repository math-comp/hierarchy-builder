{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.13";
  bundles = let common = {
      mathcomp.override.version = "hierarchy-builder-local-pack-better";
      mathcomp.job = false;
      mathcomp-single.job = true;
  }; in {
    "coq-8.13".coqPackages = {
      coq.override.version = "8.13";
      hierarchy-builder-shim.job = true;
      mathcomp-single-planB-src.job = true;
      mathcomp-single-planB.job = true;
    } // common;
    "coq-8.12".coqPackages = {
      coq.override.version = "8.12";
      coq-elpi.override.version = "v1.8";

    } // common;
    "coq-8.11".coqPackages = {
      coq.override.version = "8.11";
      coq-elpi.override.version = "v1.6";

    } // common;
  };
}
