{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-master";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "master";
      mathcomp.job = true;
      mathcomp-single.job = true;
      hierarchy-builder-shim.job = true;
      mathcomp-single-planB-src.job = true;
      graph-theory.job = false;
      fourcolor.override.version = "master";
      odd-order.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp.analyis.override.version = "hierarchy-builder";
      reglang.override.version = "master";
      coq-bits.override.version = "hierarchy-builder";
      deriving.job = false;
    };
  in {
    "coq-master".coqPackages = {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
    } // mcHBcommon;
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
