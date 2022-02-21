{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "reverse-coercions";
  # default-bundle = "master";
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
      mathcomp-finmap.override.version = "#84";
    };
  in {
    "master".coqPackages = {
      coq.override.version = "master";
      coq-elpi.override.version = "CohenCyril:nixing_around";
    } // mcHBcommon;
    "reverse-coercions".coqPackages = {
      coq.override.version = "gares:reverse-coercions";
      coq-elpi.override.version = "CohenCyril:nixing_around";
    } // mcHBcommon;
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
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
