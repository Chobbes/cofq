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
| KProd    : list KType -> KType
| KTForall : N -> list KType -> KType
| KTVar    : TypeInd -> KType (* TODO indexing for binders that bind vectors?*)
(* Base Types *)
| KIntType   : KType
.
Set Elimination Schemes.

Section KTypeInd.
  Variable P : KType -> Prop.
  Hypothesis IH_IntType         : P KIntType.
  Hypothesis IH_TVar            : forall x, P (KTVar x).
  Hypothesis IH_Prod            : forall (ts: list KType), (forall t, In t ts -> P t) -> P (KProd ts).
  Hypothesis IH_TForall  : forall (n : N) (ts: list KType), (forall t, In t ts -> P t) -> P (KTForall n ts).

  Lemma KType_ind : forall (t:KType), P t.
    fix IH 1.
    remember P as P0 in IH.
    destruct t; auto; subst.
    - apply IH_Prod.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
    - apply IH_TForall.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
  Qed.
End KTypeInd.

Inductive KValue {I} `{FInt I} : Type :=
| KAnnotated    : KType -> KRawValue -> KValue
with KRawValue {I} `{FInt I} : Type :=
| KNum          : I -> KRawValue
| KVar          : VarInd -> KRawValue
| KFix          : N -> list KType -> KTerm -> KRawValue
| KTuple        : list KValue -> KRawValue 
with KDeclaration {I} `{FInt I} : Type :=
| KVal          : KValue -> KDeclaration
| KProjN        : N -> KValue -> KDeclaration
| KOp           : PrimOp -> KValue -> KValue -> KDeclaration  
with KTerm {I} `{FInt I} : Type :=
| KLet          : KDeclaration -> KTerm -> KTerm
| KApp          : KValue -> list KType -> list KValue -> KTerm
| KIf0          : KValue -> KTerm -> KTerm -> KTerm
| KHalt         : KType -> KValue -> KTerm
.