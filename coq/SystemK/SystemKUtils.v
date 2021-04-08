From Cofq.SystemF Require Import
     SystemFDefinitions.

From Cofq.Utils Require Import
     Utils.

From Coq Require Import
     Lia
     Program.Wf.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Fixpoint term_size {I} `{FInt I} (term : Term) : nat :=
  match term with
  | Var x => 0
  | Ann e t => 1 + term_size e
  | Fix fix_type arg_type body => 1 + term_size body
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

Fixpoint type_size (τ : FType) : nat :=
  match τ with
  | Arrow a b => 1 + type_size a + type_size b
  | Prod ts => 1 + (list_sum (map type_size ts))
  | TForall x => 1 + type_size x
  | TVar x => 0
  | IntType => 0
  end.

Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate | intros; intros CONTRA; inversion CONTRA; discriminate]].
Program Fixpoint ftype_eq (τ1 : FType) (τ2 : FType) {measure (type_size τ1 + type_size τ2)} : bool
  := match τ1, τ2 with
     | Arrow a1 b1, Arrow a2 b2 => ftype_eq a1 a2 && ftype_eq b1 b2
     | Prod es1, Prod es2 =>
       zip_pred (fun τ1 τ2 => ftype_eq τ1 τ2) es1 es2
     | TForall t1, TForall t2 => ftype_eq t1 t2
     | TVar x, TVar y => N.eqb x y
     | IntType, IntType => true
     | _, _ => false
     end.
Next Obligation.
Admitted.

Program Fixpoint term_eq (e1 e2 : Term) {measure (term_size e1 + term_size e2)} : bool
  := match e1, e2 with
     | Var x, Var y => N.eqb x y
     | Ann e1 t1, Ann e2 t2 => term_eq e1 e2 && ftype_eq t1 t2
     | Fix fτ1 aτ1 body1, Fix fτ2 aτ2 body2 =>
       ftype_eq fτ1 fτ2 && ftype_eq aτ1 aτ2 && term_eq body1 body2
     | App f1 a1, App f2 a2 =>
       term_eq f1 f2 && term_eq a1 a2
     | TAbs x, TAbs y => term_eq x y
     | TApp e1 τ1, TApp e2 τ2 => term_eq e1 e2 && ftype_eq τ1 τ2
     | Tuple xs, Tuple ys =>
       zip_pred (fun e1 e2 => term_eq e1 e2) xs ys
     | ProjN i1 e1, ProjN i2 e2 =>
       N.eqb i1 i2 && term_eq e1 e2
     | Num x, Num y => eq x y
     | If0 c1 a1 b1, If0 c2 a2 b2 =>
       term_eq c1 c2 && term_eq a1 a2 && term_eq b1 b2
     | Op op1 a1 b1, Op op2 a2 b2 =>
       op_eq op1 op2 && term_eq a1 a2 && term_eq b1 b2
     | _, _ => false
     end.
Next Obligation.
  cbn.
Admitted.

Fixpoint is_value {I} `{FInt I} (e : Term) : bool :=
  match e with
  | Var x => true
  | Ann x x0 => false
  | Fix x x0 x1 => true
  | App x x0 => false
  | TAbs x => true
  | TApp x x0 => false
  | Tuple xs =>
    forallb is_value xs
  | ProjN x x0 => false
  | Num x => true
  | If0 x x0 x1 => false
  | Op x x0 x1 => false
  end.
