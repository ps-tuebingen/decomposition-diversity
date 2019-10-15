# Coding Conventions for our Coq formalization.

## General

We always use snake case (with underscores) and never camel case for all identifiers.

## Modules

Modules start with

- First the Imports from the Coq standard library.
- Then the local imports.

Question: What is the policy on reexporting modules?

## Inductive Datatypes

Inductive datatypes start with a lower-case letter.

Constructors follow the following naming convention:

- Start with an uppercase letter.
- Are prefixed by either:
  * The name of the datatype followed by an underscore.
  * A prefix of 1-3 uppercase letters which abbreviate the inductive datatype.
  
Examples:

```
Inductive nat :=
  Nat_zero ...
  Nat_succ ...

Inductive nat :=
  N_zero
  N_succ
```

## Records

The name of the records starts with an lower case letter.
If the record is called NAME, the record constructor is called mkNAME, where the first letter of the name is capitalized.

The record fields are of the following format:
- RECORDNAME_FIELDNAME
- The fieldname starts with a lower case letter and is written in snake case.

```
Record point := mkPoint {
  point_x : nat,
  point_y : nat,
  }.
```
  
  
## Fixpoints and definitions

Fixpoints and definitions are written in lower case + snake case.


## Lemmas and theorems

Lemmas and theorems are written in lower case + snake case. Except in the case were a constructor is mentioned in the name of the lemma.
In this case follow the naming scheme of the identifier.

## Proofs

Use the following levels for indentation in this order.


```
-
+
*
--
++
**
---
+++
***
```
