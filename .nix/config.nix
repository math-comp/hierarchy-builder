{
  format = "1.0.0";
  coq-attribute = "hierarchy-builder";
  namespace = ".";
  realpath = ".";
  select = "coq-8.13";
  inputs."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "gares:hierarchy-builder";
    mathcomp-single.ci = true;
  };
}
