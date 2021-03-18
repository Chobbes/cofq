From Coq Require Import
     ZArith
     List.

From Cofq.BaseExpressions Require Import
     Integers
     PrimOps.

Notation TypeInd := N.
Notation VarInd  := N.

Unset Elimination Schemes.
Inductive CType : Set :=
| CProd    : list CType -> CType
| CTForall : N -> list CType -> CType (* Combined forall / arrow type *)
| CTExists : CType -> CType
| CTVar    : TypeInd -> CType (* TODO indexing for binders that bind vectors?*)
(* Base Types *)
| CIntType   : CType
.
Set Elimination Schemes.

Section CTypeInd.
  Variable P : CType -> Prop.
  Hypothesis IH_CIntType         : P CIntType.
  Hypothesis IH_CTVar            : forall x, P (CTVar x).
  Hypothesis IH_CProd            : forall (ts: list CType), (forall t, In t ts -> P t) -> P (CProd ts).
  Hypothesis IH_CTForall  : forall (n : N) (ts: list CType), (forall t, In t ts -> P t) -> P (CTForall n ts).
  Hypothesis IH_CTExists  :  forall t, P t -> P (CTExists t).

  Lemma CType_ind : forall (t:CType), P t.
    fix IH 1.
    remember P as P0 in IH.
    destruct t; auto; subst.
    - apply IH_CProd.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
    - apply IH_CTForall.
      { revert l.
        fix IH_ts 1. intros [|u ts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IH_ts. apply Hin.
      }
    - apply IH_CTExists. auto.
  Qed.
End CTypeInd.

Inductive CValue {I} `{FInt I} : Type :=
| CAnnotated    : CRawValue -> CType -> CValue
with CRawValue {I} `{FInt I} : Type :=
| CNum          : I -> CRawValue
| CVar          : VarInd -> CRawValue
| CTuple        : list CValue -> CRawValue
| CPack         : CType -> CRawValue -> CType -> CRawValue.

Inductive CDeclaration {I} `{FInt I} : Type :=
| CVal          : CValue -> CDeclaration
| CProjN        : N -> CValue -> CDeclaration
| COp           : PrimOp -> CValue -> CValue -> CDeclaration
| CUnpack       : CRawValue -> CDeclaration
.

Inductive CTerm {I} `{FInt I} : Type :=
| CLet          : CDeclaration -> CTerm -> CTerm
| CApp          : CValue -> list CType -> list CValue -> CTerm
| CIf0          : CValue -> CTerm -> CTerm -> CTerm
| CHalt         : CValue -> CType -> CTerm
.

Inductive CHeapValue {I} `{FInt I} : Type :=
| CCode : CType -> N -> list CType -> CTerm -> CHeapValue
.

Inductive CProgram {I} `{FInt I} : Type :=
| CProg : list CHeapValue -> CProgram
.
