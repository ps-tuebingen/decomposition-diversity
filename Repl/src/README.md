# Three different representations for Expressions

```
          ---------------------------
          |      ExprParse          |
          ---------------------------
                          |
                          | Renamer.ParsedToNamed
                          |
                          V
          ---------------------------
          |      ExprNamed          |
          ---------------------------
                          |  A
                          |  |
  Renamer.NamedToDeBruijn |  | Renamer.DeBruijnToNamed
                          |  |
                          V  |
          ---------------------------
          |      ExprDB             |
          ---------------------------
                          |  A
                          |  |
  Renamer.CoqToDeBruijn   |  | Renamer.DeBruijnToCoq
                          |  |
                          V  |
          ---------------------------
          |      Coq_expr           |
          ---------------------------

```

- `ExprParse` is defined in `Parser/Definitions` and corresponds to expressions just after parsing, when destructors/consumer functions and constructors/generator functions are not yet distinguished.
- `ExprNamed` is defined in `HaskellAST` and corresponds to `ExprParse` together with the distinction between destructors/consumer functions resp. constructors/generator functions
- `ExprDB` is defined in `HaskellAST` and corresponds to a version of `ExprNamed` that has been transformed into DeBruijn representation.
- `Coq_expr` is defined in `extracted/AST.hs` and is the result of extraction from the Coq formalization.

# Parsing

Parsing a file from the disk and returning a Coq_program performs the following steps:

1. With `declarationsP` we can parse a `[Declaration]`
2. With `assembleSkeleton` we can generate from this a `Coq_skeleton`
3. The function `assembleProgram` takes a `[Declaration]` and a `Coq_skeleton`, and returns a `Coq_program`

The third step above needs to turn parsed expressions of type `ExprParse` into the corresponding datatype `Coq_expr` which is extracted from Coq. This happens in the following steps:
1. `rename` takes a `ExprParse` and a `Coq_skeleton` and returns a `ExprNamed`. `rename` resolves unqualified names into qualified names. It also finds out whether a generator/consumer is a xtor or a gfun/cfun.
2. `exprNamed2exprDB` takes a `ExprNamed` and returns a `ExprDB`, replacing named variables by de Bruijn indices.
3. `exprDB2exprCoq` takes a `ExprDB` and returns a `ExprCoq`. (This is a trivial transformation).
