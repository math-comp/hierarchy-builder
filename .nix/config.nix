{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-rev_coerce";
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
    "coq-mcHB-8.16".coqPackages = {
      coq.override.version = "8.16";
      mathcomp-analysis.override.version = "coq816";
    } // mcHBcommon;

    "coq-mcHB-8.15".coqPackages = {
      coq.override.version = "8.15";
    } // mcHBcommon;

    "coq-8.16".coqPackages = {
      coq.override.version = "8.16";
      mathcomp.override.version = "mathcomp-1.15.0";
    };
    "coq-8.15".coqPackages = {
      coq.override.version = "8.15";
    };
    "coq-rev_coerce".coqPackages = {
      coq.override.version = "proux01:rev_coerce";
      coq-elpi.override.version = "coq-master";
    };
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
