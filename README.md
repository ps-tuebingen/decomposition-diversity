# Decomposition Diversity with Symmetric Data and Codata

This is the formalization of our language with support for symmetric data and codata types.

## Formalization

The folder `Formalization` contains the Coq formalization.
An overview of the various Coq files can be found in the README.
The results of the formalization are collected in `Results.v`; please refer to this file to understand how we validated the theorems stated in our paper.
The `Makefile` for the formalization contains a target for extracting code to Haskell.

## Repl

The folder `Repl` contains a REPL (building upon a parser and prettyprinter) written in Haskell.

## Build Instructions
The Makefile provided in this (root) directory performs the following build steps:

- Build the Coq files in the `Formalization` directory
- Extract the Haskell code from the Coq code
- Copy the Haskell files into the directory `Repl/extracted`
- Use `stack` to build the REPL
- Run `stack exec Repl-exe` in the `Repl` directory

## Building without Coq
The directory `Repl/extracted` already contains Haskell files which are extracted from the Coq sources.
Instead of extracting them directly, it is possible to just run the `Makefile` in the `Repl` directory.
