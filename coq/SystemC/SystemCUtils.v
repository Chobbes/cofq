From Cofq.SystemC Require Import
     SystemCDefinitions.

From Cofq.Utils Require Import
     Utils.

From Coq Require Import
     Lia
     List
     ZArith
     Program.Wf.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Fixpoint craw_value_size {I} `{FInt I} (rv : CRawValue) : nat :=
  match rv with
  | CNum x => 0
  | CVar x => 0
  | CTuple es => 1 + (list_sum (map cvalue_size es))
  | CPack τ1 rv τ2 => 1 + craw_value_size rv
  end
with
cvalue_size {I} `{FInt I} (val : CValue) : nat :=
  match val with
  | CAnnotated rv τ => 1 + craw_value_size rv
  end.

Fixpoint cdeclaration_size {I} `{FInt I} (dec : CDeclaration) : nat :=
  match dec with
  | CVal val => 1 + cvalue_size val
  | CProjN i val => 1 + cvalue_size val
  | COp op v1 v2 => 1 + cvalue_size v1 + cvalue_size v2
  | CUnpack rv => 1 + craw_value_size rv
  end.

Fixpoint cterm_size {I} `{FInt I} (term : CTerm) : nat :=
  match term with
  | CLet dec e => 1 + cdeclaration_size dec + cterm_size e
  | CApp f τs vs => 1 + cvalue_size f + (list_sum (map cvalue_size vs))
  | CIf0 c e1 e2 => 1 + cvalue_size c + cterm_size e1 + cterm_size e2
  | CHalt e τ => 1 + cvalue_size e
  end.

Fixpoint ctype_size (τ : CType) : nat :=
  match τ with
  | CProd ts => 1 + (list_sum (map ctype_size ts))
  | CTForall n ts => 1 + (list_sum (map ctype_size ts))
  | CTExists t => 1 + ctype_size t
  | CTVar x => 0
  | CIntType => 0
  end.

Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate | intros; intros CONTRA; inversion CONTRA; discriminate]].
Program Fixpoint ftype_eq (τ1 : CType) (τ2 : CType) {measure (ctype_size τ1 + ctype_size τ2)} : bool
  := match τ1, τ2 with
     | CProd es1, CProd es2 =>
       zip_pred (fun τ1 τ2 => ftype_eq τ1 τ2) es1 es2
     | CTForall n1 ts1, CTForall n2 ts2 => zip_pred (fun τ1 τ2 => ftype_eq τ1 τ2) ts1 ts2 && N.eqb n1 n2
     | CTVar x, CTVar y => N.eqb x y
     | CIntType, CIntType => true
     | _, _ => false
     end.
Next Obligation.
Admitted.
