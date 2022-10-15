with import <nixpkgs> {};

mkShell {
    buildInputs = (with ocamlPackages; [
        ocaml dune_2 findlib
    ]);
}
