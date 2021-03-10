From Coq Require Import ZArith String List.
From QuickChick Require Export Show.

Global Open Scope string_scope.

From Cofq.BaseExpressions Require Import PrimOps.

Variant Precedence :=
| PrecOuter
| PrecMult
| PrecAdd
| PrecSub
| PrecApp
| PrecInner
.

Definition prec_value (p : Precedence) : N :=
  match p with
  | PrecOuter => 0
  | PrecAdd => 1
  | PrecSub => 1
  | PrecMult => 2
  | PrecApp => 3
  | PrecInner => 4
  end.

Definition parens (outer inner : Precedence) (s : string) :=
  if N.leb (prec_value outer) (prec_value inner)
  then s
  else "(" ++ s ++ ")".

Definition intersperse (sep : string) (l : list string) : string
  := fold_left (fun acc s => if eqb "" acc then s else s ++ sep ++ acc) l "".

Instance showPrimOp : Show PrimOp :=
  {| show :=
       fun (op : PrimOp) =>
         match op with
         | Mul => "*"
         | Add => "+"
         | Sub => "-"
         end
  |}.

Definition op_prec (op : PrimOp) : Precedence
  := match op with
     | Mul => PrecMult
     | Add => PrecAdd
     | Sub => PrecSub
     end.
