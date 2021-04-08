From Coq Require Export
     ZArith
     List.

From Cofq.BaseExpressions Require Export
     Integers
     PrimOps.

Notation TypeInd := N.
Notation VarInd  := N.

Unset Elimination Schemes.
Inductive KType : Set :=
| Prod    : list KType -> KType
| TForallVecVoid : N -> list KType -> KType
| TVar    : TypeInd -> KType (* TODO indexing for binders that bind vectors?*)
(* Base Types *)
| IntType   : KType
.
Set Elimination Schemes.

Section KTypeInd.
  Variable P : KType -> Prop.
  Hypothesis IH_IntType         : P IntType.
  Hypothesis IH_TVar            : forall x, P (TVar x).
  Hypothesis IH_Prod            : forall (ts: list KType), (forall t, In t ts -> P t) -> P (Prod ts).
  Hypothesis IH_TForallVecVoid  : forall (n : N) (ts: list KType), (forall t, In t ts -> P t) -> P (TForallVecVoid n ts).

  Lemma KType_ind : forall (t:KType), P t.
    fix IH 1.
    remember P as P0 in IH.
    destruct t; auto; subst.
    - apply IH_Prod.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
    - apply IH_TForallVecVoid.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
  Qed.
End KTypeInd.

Inductive Value {I} `{FInt I} : Type :=
| Annotated    : KType -> RawValue -> Value
with RawValue {I} `{FInt I} : Type :=
| Num          : I -> RawValue
| Var          : VarInd -> RawValue
| Fix          : N -> list KType -> Term -> RawValue
| Tuple        : list Value -> RawValue 
with Declaration {I} `{FInt I} : Type :=
| Val          : Value -> Declaration
| ProjN        : N -> Value -> Declaration
| Op           : PrimOp -> Value -> Value -> Declaration  
with Term {I} `{FInt I} : Type :=
| Let          : Declaration -> Term -> Term
| App          : Value -> list KType -> list Value -> Term
| If0          : Value -> Term -> Term -> Term
| Halt         : KType -> Value -> Term
.