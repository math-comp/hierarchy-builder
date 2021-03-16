{
  format = "1.0.0";
  coq-attribute = "hierarchy-builder";
  namespace = "HB";
  realpath = ".";
  select = "coq-8.13";
  inputs."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "hierarchy-builder";
    mathcomp-single.ci.step = true;
  };
}
