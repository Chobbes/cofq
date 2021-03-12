From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Numeric.Integers
     Utils.Util.

From Coq Require Import
     List.

From Cofq.BaseExpressions Require Import
     PrimOps
     Integers.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Definition genInt64 : G Int64.int
  := z <- arbitrary;;
     ret (Int64.repr z).

Definition genPrimOp : G PrimOp
  := oneOf_ failGen (map returnGen [Mul; Add; Sub]).
