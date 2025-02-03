{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "coq-8.20";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "master";
      mathcomp.job = true;
      mathcomp-single.job = true;
      graph-theory.job = false;
      fourcolor.override.version = "master";
      odd-order.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp-classical.override.version = "master";
      mathcomp-analysis.override.version = "master";
      reglang.override.version = "master";
      coq-bits.override.version = "master";
      deriving.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      multinomials.override.version = "master";
      mathcomp-real-closed.override.version = "master";
      coqeal.override.version = "master";
    };
  in {
    "coq-master".coqPackages = mcHBcommon // {
      coq.override.version = "master";
      stdlib.override.version = "master";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "2.0.7";
      bignums.override.version = "master";
    };

    "coq-9.0".coqPackages = mcHBcommon // {
      coq.override.version = "9.0";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "2.0.7";
    };

    "coq-8.20".coqPackages = mcHBcommon // {
      coq.override.version = "8.20";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "2.0.7";
    };

    "coq-8.19".coqPackages = mcHBcommon // {
      coq.override.version = "8.19";
      coqeal.job = false;  # requries Coq >= 8.20 through coq-elpi master
    };

    "coq-8.18".coqPackages = mcHBcommon // {
      coq.override.version = "8.18";
      mathcomp-classical.job = false;  # Analysis master dropped suppor for 8.18
      mathcomp-analysis.job = false;
      coqeal.job = false;  # requries Coq >= 8.20 through coq-elpi master
    };

  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
