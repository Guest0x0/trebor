with import <nixpkgs>; {}

mkShell {
    buildInputs = (with ocamlPackages; [
        ocaml dune_d findlib
    ]);
}
