# Formalization of total Defunctionalization / Refunctionalization

## Dependencies


## Overview of the Formalization

The most important parts of the formalization are contained in the following files.
Please note that this file (and the whole formalization) uses the terms de- and
refunctionalization instead of the terms constructorization and
destructorization used in the paper.

### AST.v

Contains the definition of the abstract syntax of expressions.
Expressions are formalized with de Bruijn indices.

### UtilsAST.v

Contains various utilities for working with expressions:

- Definition and lemmas about equality of names, qualified names and scoped names.
- Substitution of expressions for variables in expressions.
- A custom induction principle for expressions. This is necessary since expressions are a nested inductive data type.

### ProgramSkeleton.v

Contains the definition of the ProgramSkeleton, which is formalized as a dependent record.
The ProgramSkeleton contains the datatypes and constructors, the codatatypes and destructors, and the signatures of all
functions, generator functions and consumer functions contained in the program.

```
Record ProgramSkeleton : Type := mkProgramSkeleton {
...
}
```

There are special fields in the dependent record which contain proofs that wellformededness conditions of the ProgramSkeleton are
satisfied, e.g. that names of functions are unique.

### UtilsSkeleton.v

Contains functions for looking up information in a ProgramSkeleton, such as looking up the constructors of a datatype.

### UBProgram.v

Contains the definition of a program.

```
Record Program : Type := mkProgram {
...
}.
```

A program is a ProgramSkeleton, together with bodies for all signatures contained in the ProgramSkeleton.

### Typechecker.v

Contains both:

- A function `typecheck'` which given an expression e, a ProgramSkeleton ps and a typing context ctx returns a `option TypeName`
- An inductive relation `TypeDeriv` formalizing the typing rules for expressions.

```
Fixpoint typecheck' (ps : ProgramSkeleton) (ctx : Ctxt) (e : Expr) {struct e} : option TypeName :=
...

Inductive TypeDeriv : ProgramSkeleton -> Ctxt -> Expr -> TypeName -> Prop :=
...
where "p '/' c '|-' e ':' t" := (TypeDeriv p c e t)
```

There is one theorem stating that the typecheck function is correct:

```
Theorem typecheck_correct : forall (prog : ProgramSkeleton) (ctx : Ctxt) (e : Expr) (t : TypeName),
    typecheck' prog ctx e = Some t ->
    prog / ctx |- e : t.
```

and one theorem stating that the typecheck function is complete:

```
Theorem typecheck_complete : forall (prog : ProgramSkeleton) (ctx : Ctxt) (e : Expr) (tn : TypeName),
    prog / ctx |- e : tn ->
  typecheck' prog ctx e = Some tn
```

### Eval.v

Contains the definition of values both as a function and inductive relation:

```
Fixpoint value_b (e : Expr) : bool :
...
Inductive value : Expr -> Prop :=
...
Fixpoint value_reflect (e : Expr) : reflect (value e) (value_b e).
...
```

Contains the definition of a single step evaluation function:

```
Fixpoint one_step_eval (p : Program) (e : Expr) {struct e} : option Expr :=
```

together with an inductive relation:

```
Inductive step : Program -> Expr -> Expr -> Prop :=
...
where "'[' prog '|-' e '==>' e' ']'" := (step prog e e') : eval_scope.
```

Together with proofs of the correctness and completeness of the inductive relation w.r.t to the
function:

```
Theorem eval_complete : forall (prog : Program) (e1 e2 : Expr),
    [ prog |- e1 ==> e2 ] ->
    one_step_eval prog e1 = Some e2.
	
Theorem eval_correct : forall (prog : Program) (e e' : Expr),
    one_step_eval prog e = Some e' ->
    [ prog |- e ==> e' ].
```

### Progress.v

Contains the proof of the progress property:

```
Theorem progress : forall (e : Expr) (p : Program) (tc : exists t, (skeleton p) / [] |- e : t),
    value_b e = true <-> one_step_eval p e = None.
```

### Preservation.v

Contains the proof of the preservation property:

```
Theorem preservation : forall (p : Program) (e1 e2 : Expr) (t : TypeName),
    ((skeleton p) / [] |- e1 : t) ->
    [ p |- e1 ==> e2 ] ->
    (skeleton p) / [] |- e2 : t.
```

### DefuncI.v

Contains Stage I of the algorithm: the computation of the new program skeleton.

```
Definition defunctionalizeToSkeleton (p : Program) (n : TypeName) : ProgramSkeleton :=
```

### DefuncII.v and DefuncIII.v

Contain Stage II of the algorithm: the computation of the new function bodies.
