{
  format = "1.0.0";
  attribute = "hierarchy-builder";
  default-bundle = "rocq-9.1";
  bundles = let
    mcHBcommon = {
      mathcomp.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp-real-closed.override.version = "master";
      mathcomp-analysis.override.version = "master";
    };
    coqMcHBcommon = {
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
      mathcomp-zify.override.version = "master";
      mathcomp-algebra-tactics.override.version = "master";
      mathcomp-word.override.version = "master";
      coquelicot.override.version = "master";
      ExtLib.override.version = "master";
      simple-io.override.version = "master";
      QuickChick.override.version = "master";
      # jasmin.override.version = "main";
      jasmin.job = false;  # currently broken
      autosubst.job = false;
      ConCert.job = false;
      interval.job = false;
    };
  in {
    "rocq-master" = { rocqPackages = mcHBcommon // {
      rocq-core.override.version = "master";
      stdlib.override.version = "master";
      rocq-elpi.override.version = "master";
      micromega-plugin.override.version = "master";
      bignums.override.version = "master";
    }; coqPackages = coqMcHBcommon // {
      coq.override.version = "master";
      stdlib.override.version = "master";
      coq-elpi.override.version = "master";
      bignums.override.version = "master";
      coquelicot.job = false;
    }; };

    "rocq-9.2" = { rocqPackages = mcHBcommon // {
      rocq-core.override.version = "9.2";
      micromega-plugin.override.version = "master";
      micromega-plugin.job = false;
    }; coqPackages = coqMcHBcommon // {
      coq.override.version = "9.2";
    }; };

    "rocq-9.1" = { rocqPackages = mcHBcommon // {
      rocq-core.override.version = "9.1";
    }; coqPackages = coqMcHBcommon // {
      coq.override.version = "9.1";
    }; };

    "rocq-9.0" = { rocqPackages = mcHBcommon // {
      rocq-core.override.version = "9.0";
    }; coqPackages = coqMcHBcommon // {
      coq.override.version = "9.0";
    }; };
  };
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

}
