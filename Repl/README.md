# UroboroRepl

## Extracted Haskell Code
The Haskell files in the subdirectory `extracted` should not be modified, since they are automatically extracted from the Coq formalization.

## Build Instructions
In order to keep the Coq formalization and the Haskell code in sync, do not build these files yourself.
Use the `Makefile` in the parent directory.

## Usage
The REPL can be run via `stack exec Repl`.
Help is available by typing `:help` inside the REPL.

Typing `:load <filename>` will load the program in the given file inside the REPL and typecheck it.
Example files are located in the `examples/` directory.
The last-used file can be reloaded with `:reload`.
To print the current program, type `:showprogram`.
Writing an expression which is valid within the currently loaded program will evaluate this expression.
Alternatively, you can evaluate an expression `<expr>` for `<n>` steps by using `:step <n> <expr>`.

_Missing:_
 - _xfunc_
 - _declare_
 
 ### Options
 There are several options which change the REPL's behaviour.
 These options can be set and unset using `:set <option>` and `:unset <option>`, respectively.
  - `printNat`: print values of type `Nat` as numerals instead of their unary representations
  - `printDeBruijn`: print deBruijn index of variables (mostly for debugging)
  - `printQualifiedNames`: add the type name of an xtor before its name as a qualifier.
