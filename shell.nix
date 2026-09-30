{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    buildInputs = with pkgs; [
      # Rust
      bacon
      cargo
      clippy
      rustfmt
      rustc
      # TODO: add rust-src
    ];

  }
