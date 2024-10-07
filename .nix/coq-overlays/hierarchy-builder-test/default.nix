{ hierarchy-builder, coqPackages }:

coqPackages.lib.overrideCoqDerivation {
  pname = "hierarchy-builder-test";

  buildFlags = [ "test-suite" ];
} hierarchy-builder
