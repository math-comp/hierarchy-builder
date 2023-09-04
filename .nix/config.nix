{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.16";
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
      interval.override.version = "master";
      reglang.override.version = "master";
      coq-bits.override.version = "hierarchy-builder";
      deriving.job = false;
    };
  in {
    "coq-master".coqPackages = mcHBcommon // {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      interval.job = false;
    };

    "coq-8.17".coqPackages = mcHBcommon // {
      coq.override.version = "8.17";
    };

    "coq-8.16".coqPackages = mcHBcommon // {
      coq.override.version = "8.16";
    };

    "coq-8.15".coqPackages = mcHBcommon // {
      coq.override.version = "8.15";
      mathcomp.job = false;
      mathcomp-infotheo.job = false;
    };
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
