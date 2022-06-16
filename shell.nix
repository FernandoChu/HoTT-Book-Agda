with (import <nixpkgs> { });
let
  oldPkgs = import
    (builtins.fetchGit {
      # Descriptive name to make the store path easier to identify                
      name = "my-old-revision";
      url = "https://github.com/NixOS/nixpkgs/";
      ref = "refs/heads/nixpkgs-unstable";
      # Search for the revision for the agda versions in
      # https://lazamar.co.uk/nix-versions/?channel=nixpkgs-unstable&package=agda
      rev = "bf972dc380f36a3bf83db052380e55f0eaa7dcb6";
    })
    { };
in
mkShell {
  # nativeBuildInputs is usually what you want -- tools you need to run
  buildInputs = [
    (oldPkgs.agda.withPackages (p: [
      (p.standard-library.overrideAttrs (oldAttrs: {
        version = "1.7";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v1.7";
          sha256 = "sha256-Wv5/pMe4MI0Z/XdDUsaNtpudbFdFbHNKekQkU/OVA5I=";
        };
      }))
    ]))
  ];
}

