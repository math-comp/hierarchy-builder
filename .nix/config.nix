{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-master";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "hierarchy-builder";
      mathcomp.job = true;
      mathcomp-single.job = true;
      hierarchy-builder-shim.job = true;
      mathcomp-single-planB-src.job = true;
      mathcomp-single-planB.job = true;
      graph-theory.job = false;
      fourcolor.override.version = "master";
      odd-order.override.version = "hirarchy-builder";
      mathcomp-finmap.override.version = "proux01:hierarchy-builder";
      mathcomp.analyis.override.version = "#694";
    };
  in {
    "coq-mcHB-master".coqPackages = {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
    } // mcHBcommon;
    "coq-mcHB-master".ocamlPackages = {
      elpi.override.version = "1.16.5";
    };
    "coq-master".coqPackages = {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
    };
    "coq-master".ocamlPackages = {
      elpi.override.version = "1.16.5";
    };
  };
  cachix.coq = {};
  cachix.coq-community = {};
   cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
