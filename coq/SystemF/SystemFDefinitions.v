From Coq Require Export
     ZArith
     List.

From Cofq.BaseExpressions Require Export
     Integers
     PrimOps.

Notation TypeInd := N.
Notation VarInd  := N.

Unset Elimination Schemes.
Inductive FType : Set :=
| Arrow   : FType -> FType -> FType
| Prod    : list FType -> FType
| TForall : FType -> FType
| TVar    : TypeInd -> FType
(* Base Types *)
| IntType   : FType
.
Set Elimination Schemes.

Section FTypeInd.
  Variable P : FType -> Prop.
  Hypothesis IH_IntType       : P IntType.
  Hypothesis IH_TVar          : forall x, P (TVar x).
  Hypothesis IH_Prod          : forall (ts: list FType), (forall t, In t ts -> P t) -> P (Prod ts).
  Hypothesis IH_Arrow         : forall t1 t2, P t1 -> P t2 -> P (Arrow t1 t2).
  Hypothesis IH_TForall       : forall t, P t -> P (TForall t).

  Lemma FType_ind : forall (t:FType), P t.
    fix IH 1.
    remember P as P0 in IH.
    destruct t; auto; subst.
    - apply IH_Arrow; auto.
    - apply IH_Prod.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
    - apply IH_TForall. auto.
  Qed.
End FTypeInd.

Inductive Term {I} `{FInt I} : Type :=
| Var          : VarInd -> Term
(* Annotated terms *)
| Ann          : Term -> FType -> Term
(* Terms *)
| Fix          : FType -> FType -> Term -> Term
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
