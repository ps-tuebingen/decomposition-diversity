# Decomposition Diversity REPL

## Build Instructions

Building the REPL locally requires that `stack` is installed on your computer.

Use

```console
stack build
stack exec Repl
```
to build and run the REPL.

## Usage

Help is available by typing `:help` inside the REPL.

- Typing `:load <filename>` will load the program in the given file inside the REPL and typecheck it.
  Example files are located in the `examples/` directory.
- The last-used file can be reloaded with `:reload`.
- To print the current program, type `:showprogram`.
- Writing an expression which is valid within the currently loaded program will evaluate this expression.
  Alternatively, you can evaluate an expression `<expr>` for `<n>` steps by using `:step <n> <expr>`.
  In the expression, you may also write numerals for values of type `Nat` (when such a type exists and represents the usual Peano numbers).
  Additionally, `:{` or `:multiline` will start a multiline mode, which allows writing an expression spanning multiple lines.
  To end the input, write `:}` in a separate new line.
- To add a declaration to the program, use :declare.
  This will start multiline mode, which can be used to define a new declaration to be added to the program.
  To end the input, write `:}` in a separate new line.
  Afterwards, the new program is typechecked. If this succeeds, the loaded program is updated.
- To constructorize the currently loaded program, type `:constructorize <x>`, where `<x>` is the codatatype to be constructorized.
- To destructorize the currently loaded program, type `:destructorize <x>`, where `<x>` is the datatype to be destructorized.
- To transpose the currently loaded program, type `:transpose <x>`, where `<x>` is the xDatatype to be transpose.
  The REPL will figure out which direction is required when tranposing.
 
 ### Options
 There are several options which change the REPL's behaviour.
 These options can be set and unset using `:set <option>` and `:unset <option>`, respectively.
  - `printNat`: print values of type `Nat` as numerals instead of their unary representations
  - `printDeBruijn`: print deBruijn index of variables (mostly for debugging)
  - `printQualifiedNames`: add the type name of an xtor before its name as a qualifier.
