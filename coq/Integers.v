From Vellvm Require Import
     Numeric.Integers.

Class FInt I : Type :=
  { add  : I -> I -> I;
    sub  : I -> I -> I;
    mul  : I -> I -> I;
    eq   : I -> I -> bool;
    zero : I;
  }.

Instance FInt64 : FInt Int64.int :=
  {| add  := Int64.add;
     sub  := Int64.sub;
     mul  := Int64.mul;
     eq   := Int64.eq;
     zero := Int64.zero;
  |}.

Inductive PrimOp : Set :=
| Mul
| Add
| Sub
.
