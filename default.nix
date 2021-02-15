{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci ? false, ci-step ? null, inNixShell ? null
}@args:
let src = fetchGit "https://github.com/coq-community/nix-toolbox.git"; in
(import "${src}/auto-config.nix" ./. args).nix-auto

