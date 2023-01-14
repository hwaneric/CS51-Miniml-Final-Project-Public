
## Overview



This repository contains my final project for Harvard's CS51 course. For my final project, I implemented a very minimal coding language called miniml that runs within OCaml as an interpreter. This Turing complete language includes support for a subset of constructs and a limited number of types. There are options to run the language using either subsititution model, dynamically scoped enivornment, or lexically scoped environment semantics. 





## Usage

### Performing evaluations using miniml.
1. Compile the miniml.ml folder with the following command.
```bash
ocamlbuild -use-ocamlfind miniml.byte
```

2. Open the REPL that miniml runs on.
```bash
./miniml.byte
```

### Switching between substitution model, dynamically scoped environment, and lexically scoped environment semantics.
1. Change the ```evaluate``` variable at the bottom of the evaluation.ml file to the appropriate function (```eval_s``` for substitution model, ```eval_d``` for dynamically scoped environments, and ```eval_l``` for lexically scoped environments). 
```bash
# Substitution Model
let evaluate = eval_s ;;

# Dynamically Scoped Environments Model
let evaluate = eval_d ;;

# Lexically Scoped Environments Model
let evaluate = eval_l ;;
```

