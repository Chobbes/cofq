From Cofq.BaseExpressions Require Import Integers.

Inductive PrimOp : Set :=
| Mul
| Add
| Sub
.

Definition eval_primop {I} `{FInt I} (op : PrimOp) : (I -> I -> I) :=
  match op with
  | Mul => mul
  | Add => add
  | Sub => sub
  end.

Definition eval_op {I} `{FInt I} (op : PrimOp) (x y : I) : I :=
  eval_primop op x y.

Definition op_eq (op1 op2 : PrimOp) : bool
  := match op1, op2 with
     | Mul, Mul => true
     | Add, Add => true
     | Sub, Sub => true
     | _, _ => false
     end.
