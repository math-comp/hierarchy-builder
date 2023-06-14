{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.16";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "hierarchy-builder";
      mathcomp.job = true;
      mathcomp-single.job = true;
      hierarchy-builder-shim.job = true;
      mathcomp-single-planB-src.job = true;
      graph-theory.job = false;
      fourcolor.override.version = "master";
      odd-order.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp.analyis.override.version = "hierarchy-builder";
      interval.override.version = "master";
      reglang.override.version = "hierarchy-builder";
      coq-bits.override.version = "hierarchy-builder";
      deriving.job = false;
    };
  in {
    "coq-8.17".coqPackages = {
      coq.override.version = "8.17";
    } // mcHBcommon;

    "coq-8.16".coqPackages = {
      coq.override.version = "8.16";
    } // mcHBcommon;

    "coq-8.15".coqPackages = {
      coq.override.version = "8.15";
      mathcomp.job = false;
      mathcomp-infotheo.job = false;
    };
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
