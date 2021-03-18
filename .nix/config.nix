{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-task = "coq-8.13";
  tasks = let common = {
      mathcomp.override.version = "hierarchy-builder";
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
    } // common;
    "coq-8.11".coqPackages = {
      coq.override.version = "8.11";
      coq-elpi.override.version = "v1.6.1_8.11";
    } // common;
  };
}
