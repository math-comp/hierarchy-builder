{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci ? false, ci-step ? null, inNixShell ? null
}@args:
let src = fetchGit {
  url = "https://github.com/coq-community/coq-nix-toolbox.git";
  ref = "8b8ed7f4fc38ae218d99fe9909142b30e6a0733f";
}; in
(import src ./. args).nix-auto

