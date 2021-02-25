From Coq Require Import
     ZArith
     String
     List.

From Vellvm Require Import
     Numeric.Integers
     Utils.Util.

Require Import Lia.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From ITree Require Import
     Basics
     ITree
     Interp.Recursion
     Events.Exception.

Import MonadNotation.
Local Open Scope monad_scope.


Notation TypeInd := N.
Notation VarInd  := N.

Class FInt I : Type :=
  { add  : I -> I -> I;
    sub  : I -> I -> I;
    mul  : I -> I -> I;
    eq   : I -> I -> bool;
    zero : I;
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

Inductive Term {I} `{FInt I} : Type :=
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
| Num          : I -> Term
(* Expressions *)
| If0          : Term -> Term -> Term -> Term
| Op           : PrimOp -> Term -> Term -> Term
.

Definition TypeContext := N.
Definition TermContext := list FType.

Fixpoint term_size {I} `{FInt I} (term : Term) : nat :=
  match term with
  | Var x => 0
  | Ann e t => 1 + term_size e
  | Fix arg_type body => 1 + term_size body
  | App e1 e2 => 1 + term_size e1 + term_size e2
  | TAbs e => 1 + term_size e
  | TApp e t => 1 + term_size e
  | Tuple es => 1 + (list_sum (map term_size es))
  | ProjN i e => 1 + term_size e
  | Num x => 0
  | If0 c e1 e2 => 1 + term_size c + term_size e1 + term_size e2
  | Op op e1 e2 => 1 + term_size e1 + term_size e2
  end
  .

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

Definition eval_op {I} `{FInt I} (op : PrimOp) (x y : I) : I :=
  eval_primop op x y.

Definition app_fix {I} `{FInt I} (arg_type : FType) (body : Term) (arg : Term) : Term :=
  term_subst 1 (term_subst 0 body (Fix arg_type body)) arg.

Lemma list_sum_map :
  forall {X} (f : X -> nat) x xs,
    In x xs ->
    list_sum (map f xs) >= f x.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs H).
    unfold list_sum in IHxs.
    lia.
Qed.

Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]].
Program Fixpoint step {I} `{FInt I} (e : Term) {measure (term_size e)} : (unit + Term) :=
  match e with
  | Ann e t => step e
  | Fix arg_type body => inl tt
  | App (Fix arg_type body) arg =>
    inr (app_fix arg_type body arg)
  | App e1 e2 =>
    e1v <- step e1;;
    inr (App e1v e2)
  | Op op (Num xn) (Num yn) =>
    inr (Num (eval_op op xn yn))
  | Op op (Num xn) y =>
    yv <- step y ;;
    inr (Op op (Num xn) yv)
  | Op op x y =>
    xv <- step x ;;
    inr (Op op xv y)
  | TApp x t => inl tt (* TODO: Unimplemented *)
  | ProjN i (Tuple es) =>
    match nth_error es (N.to_nat i) with
    | Some e => step e
    | None => inl tt
    end
  | ProjN i e =>
    ev <- step e;;
    inr (ProjN i ev)
  | If0 (Num x) e1 e2 =>
    if eq x zero
    then inr e1
    else inr e2
  | If0 c e1 e2 =>
    cv <- step c;;
    inr (If0 cv e1 e2)
  | _ => inl tt
  end.
Next Obligation.
  cbn.
  symmetry in Heq_anonymous.
  apply nth_error_In in Heq_anonymous.
  pose proof (list_sum_map term_size e es Heq_anonymous).       
  lia.
Qed.

Definition Failure := exceptE string.
Open Scope string_scope.

Definition eval_body {I} `{FInt I} (e : Term) : itree (callE Term Term +' Failure) Term :=
  match e with
  | Ann e t => call e
  | App e1 e2 =>
    e1v <- call e;;
    e2v <- call e2;;
    match e1v with
    | Fix arg_type body => ret (app_fix arg_type body e2v)
    | _ => throw "ill-typed application"
    end
  | TApp e t => throw "unimplemented"
  | ProjN i es =>
    es' <- call es;;
    match es' with
    | Tuple xs =>
      xs' <- map_monad call xs;;
      match nth_error xs' (N.to_nat i) with
      | Some e => call e
      | None => throw "tuple projection out of bounds"
      end
    | _ => throw "ill-typed tuple projection"
    end
  | If0 c e1 e2 =>
    cv <- call c;;
    match cv with
    | Num x =>
      if eq x zero
      then call e1
      else call e2
    | _ => throw "ill-typed if0"
    end
  | Op op e1 e2 =>
    e1v <- call e1;;
    e2v <- call e2;;
    match e1v, e2v with
    | Num x, Num y =>
      ret (Num (eval_op op x y))
    | _, _ => throw "ill-typed operation"
    end
  | Num x => ret e
  | TAbs x => ret e
  | Tuple x => ret e
  | Fix arg_type body => ret e
  | Var x => ret e
  end.

Definition eval {I} `{FInt I} : Term -> itree Failure Term :=
  rec eval_body.
