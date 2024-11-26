{ repoRoot, inputs, pkgs, lib, system }:

let

  cabalProject = pkgs.haskell-nix.cabalProject' {
    name = "escrow";
    src = ../.;
    compiler-nix-name = lib.mkDefault "ghc96";
    shell.withHoogle = false;
    inputMap = {
      "https://chap.intersectmbo.org/" = inputs.iogx.inputs.CHaP;
    };
    modules = [{
      packages = {
        # Werror everything. This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519
        escrow.ghcOptions = [ "-Werror" ];
      };
    }];
  };

  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    shellArgs = repoRoot.nix.shell;
    readTheDocs = {
      enable = true;
      siteFolder = "doc/read-the-docs-site";
    };
  };

in

project
