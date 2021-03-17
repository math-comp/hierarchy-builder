{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-task = "coq-8.13";
  tasks."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "hierarchy-builder";
    mathcomp.job = false;
    mathcomp-single.job = true;
    hierarchy-builder-shim.job = true;
    mathcomp-single-planB-src.job = true;
    mathcomp-single-planB.job = true;
  };
}
