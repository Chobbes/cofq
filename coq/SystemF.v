From Coq Require Import
     ZArith
     List.

Require Import Vellvm.Numeric.Integers.

Notation TypeInd := N.
Notation VarInd  := N.

Class FInt I : Type :=
  { add : I -> I -> I;
    sub : I -> I -> I;
    mul : I -> I -> I;
  }.

Inductive FType : Set :=
| Arrow   : FType -> FType -> FType
| Prod    : list FType -> FType
| TForall : FType -> FType
| TVar    : TypeInd -> FType
(* Base Types *)
| IntType   : FType
.

Inductive PrimOp : Set :=
| Mul
| Add
| Sub
.

Inductive Term {I} `{FInt I} : Set :=
| Var          : VarInd -> Term
(* Annotated terms *)
| Ann          : Term -> FType -> Term
(* Terms *)
| Fix          : FType -> Term -> Term
| App          : Term -> Term -> Term
(* Type stuff *)
| TAbs         : Term -> Term
| TApp         : Term -> FType -> Term
(* Prod *)
| Tuple        : list Term -> Term 
| ProjN        : N -> Term -> Term
(* Int *)
| Num          : Int64.int -> Term
(* Expressions *)
| If0          : Term -> Term -> Term -> Term
| Op           : PrimOp -> Term -> Term -> Term
.

Definition TypeContext := N.
Definition TermContext := list FType.

(* Lift by 2 because fixpoint has a argument in addition to referring to itself *)
Fixpoint term_lift {I} `{FInt I} (n : N) (term : Term) : Term :=
  match term with
  | Var x =>
    if N.ltb x n
    then Var x
    else Var (x + 2)
  | Ann term' type => Ann (term_lift n term') type
  | Fix ftype fbody => Fix ftype (term_lift (n+2) fbody)
  | App e1 e2 => App (term_lift n e1) (term_lift n e2)
  | TAbs e => TAbs (term_lift n e)
  | TApp e t => TApp (term_lift n e) t
  | Tuple es => Tuple (map (term_lift n) es)
  | ProjN i es => ProjN i (term_lift n es)
  | Num x => Num x
  | If0 c e1 e2 => If0 (term_lift n c) (term_lift n e1) (term_lift n e2)
  | Op op e1 e2 => Op op (term_lift n e1) (term_lift n e2)
  end.

Fixpoint term_subst {I} `{FInt I} (v : VarInd) (body arg : Term) : Term :=
  match body with
  | Var x =>
    if N.eqb x v
    then arg
    else Var x
  | Fix farg fbody =>
    Fix farg (term_subst (v + 2) fbody (term_lift 0 arg))
  | Ann e t => Ann (term_subst v e arg) t
  | App e1 e2 => App (term_subst v e1 arg) (term_subst v e2 arg)
  | TAbs e => TAbs (term_subst v e arg)
  | TApp e t => TApp (term_subst v e arg) t
  | Tuple es => Tuple (map (fun e => term_subst v e arg) es)
  | ProjN i e => ProjN i (term_subst v e arg)
  | Num x => Num x
  | If0 c e1 e2 => If0 (term_subst v c arg) (term_subst v e1 arg) (term_subst v e2 arg)
  | Op op e1 e2 => Op op (term_subst v e1 arg) (term_subst v e2 arg)
  end.

Definition eval_primop {I} `{FInt I} (op : PrimOp) : (I -> I -> I) :=
  match op with
  | Mul => mul
  | Add => add
  | Sub => sub
  end.

Definition eval_op {I } `{FInt I} (op : PrimOp) (x y : I) : I :=
  eval_primop op x y.
