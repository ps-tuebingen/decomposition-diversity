# Decomposition Diversity with Symmetric Data and Codata

This is the formalization of our language with support for symmetric data and codata types.

## Formalization

The folder `Formalization` contains the Coq Formalization. The results of the formalization are collected in Results.v.
The Makefile for the formalization contains a target for extracting code to Haskell.

## Repl

The folder `Repl` contains a Repl, Parser and PrettyPrinter written in Haskell.

## Build Instructions
The Makefile provided in this (root) directory performs the following build steps:

- Build the Coq Files in the "Formalization" directory
- Extract the Haskell Code from the Coq Code
- Copy the Haskell files into the directory "Repl/extracted"
- Use stack to build the Repl
- Run "stack exec Repl-exe" in the Repl directory

## Building without Coq
The directory "Repl/extracted" already contains Haskell files which are extracted from the Coq sources.
Instead of extracting them directly, it is possible to just run the Makefile in the "Repl" directory.
