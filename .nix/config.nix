{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.18";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "master";
      mathcomp.job = true;
      mathcomp-single.job = true;
      graph-theory.job = false;
      fourcolor.override.version = "master";
      odd-order.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp.analyis.override.version = "hierarchy-builder";
      interval.override.version = "master";
      reglang.override.version = "master";
      coq-bits.override.version = "hierarchy-builder";
      deriving.job = false;
      mathcomp-bigenough.override.version = "master";
      multinomials.override.version = "master";
      mathcomp-real-closed.override.version = "master";
      coqeal.override.version = "master";
    };
  in {
    "coq-master".coqPackages = mcHBcommon // {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      bignums.override.version = "master";
      paramcoq.override.version = "master";
      interval.job = false;
    };

    "coq-8.18".coqPackages = mcHBcommon // {
      coq.override.version = "8.18";
      interval.job = false;
      coq-elpi.override.version = "fix-synterp";
    };

    # "coq-8.17".coqPackages = mcHBcommon // {
    #   coq.override.version = "8.17";
    # };
# 
    # "coq-8.16".coqPackages = mcHBcommon // {
    #   coq.override.version = "8.16";
    # };
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
