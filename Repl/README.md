# "Decomposition Diversity" REPL

## Extracted Haskell Code
The Haskell files in the subdirectory `extracted` should not be modified, since they are automatically extracted from the Coq formalization.

## Build Instructions
In order to keep the Coq formalization and the Haskell code in sync, do not build these files yourself.
Use the `Makefile` in the parent directory.

## Usage
The REPL can be run via `stack exec Repl`.
Help is available by typing `:help` inside the REPL.

- Typing `:load <filename>` will load the program in the given file inside the REPL and typecheck it.
  Example files are located in the `examples/` directory.
- The last-used file can be reloaded with `:reload`.
- To print the current program, type `:showprogram`.
- Writing an expression which is valid within the currently loaded program will evaluate this expression.
  Alternatively, you can evaluate an expression `<expr>` for `<n>` steps by using `:step <n> <expr>`.
  In the expression, you may also write numerals for values of type `Nat` (when such a type exists and represents the usual Peano numbers).
- To constructorize the currently loaded program, type `:constructorize <x>`, where `<x>` is the codatatype to be constructorized.
- To destructorize the currently loaded program, type `:destructorize <x>`, where `<x>` is the datatype to be destructorized.

_Missing:_
 - _declare_
 
 ### Options
 There are several options which change the REPL's behaviour.
 These options can be set and unset using `:set <option>` and `:unset <option>`, respectively.
  - `printNat`: print values of type `Nat` as numerals instead of their unary representations
  - `printDeBruijn`: print deBruijn index of variables (mostly for debugging)
  - `printQualifiedNames`: add the type name of an xtor before its name as a qualifier.
