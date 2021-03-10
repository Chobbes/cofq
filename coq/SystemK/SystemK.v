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

(* Needed for the Show typeclass *)
From QuickChick Require Import QuickChick.

From Cofq.BaseExpressions Require Import
     Integers
     PrimOps.

From Cofq.SystemF Require Import SystemF.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

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
| Fix          : list KType -> list KType -> Term -> RawValue
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

(* Fixpoint term_size {I} `{FInt I} (term : Term) : nat := *)
(*   match term with *)
(*   | Var x => 0 *)
(*   | Ann e t => 1 + term_size e *)
(*   | Fix fix_type arg_type body => 1 + term_size body *)
(*   | App e1 e2 => 1 + term_size e1 + term_size e2 *)
(*   | TAbs e => 1 + term_size e *)
(*   | TApp e t => 1 + term_size e *)
(*   | Tuple es => 1 + (list_sum (map term_size es)) *)
(*   | ProjN i e => 1 + term_size e *)
(*   | Num x => 0 *)
(*   | If0 c e1 e2 => 1 + term_size c + term_size e1 + term_size e2 *)
(*   | Op op e1 e2 => 1 + term_size e1 + term_size e2 *)
(*   end *)
(* . *)

(* Fixpoint type_size (τ : FType) : nat := *)
(*   match τ with *)
(*   | Arrow a b => 1 + type_size a + type_size b *)
(*   | Prod ts => 1 + (list_sum (map type_size ts)) *)
(*   | TForall x => 1 + type_size x *)
(*   | TVar x => 0 *)
(*   | IntType => 0 *)
(*   end. *)

(* (* Lift by 2 because fixpoint has a argument in addition to referring to itself *) *)
(* Fixpoint term_lift {I} `{FInt I} (n : N) (term : Term) : Term := *)
(*   match term with *)
(*   | Var x => *)
(*     if N.ltb x n *)
(*     then Var x *)
(*     else Var (x + 2) *)
(*   | Ann term' type => Ann (term_lift n term') type *)
(*   | Fix fix_type arg_type fbody => Fix fix_type arg_type (term_lift (n+2) fbody) *)
(*   | App e1 e2 => App (term_lift n e1) (term_lift n e2) *)
(*   | TAbs e => TAbs (term_lift n e) *)
(*   | TApp e t => TApp (term_lift n e) t *)
(*   | Tuple es => Tuple (map (term_lift n) es) *)
(*   | ProjN i es => ProjN i (term_lift n es) *)
(*   | Num x => Num x *)
(*   | If0 c e1 e2 => If0 (term_lift n c) (term_lift n e1) (term_lift n e2) *)
(*   | Op op e1 e2 => Op op (term_lift n e1) (term_lift n e2) *)
(*   end. *)

(* Fixpoint type_lift (n : N) (τ : FType) : FType := *)
(*   match τ with *)
(*   | Arrow τ1 τ2 => Arrow (type_lift n τ1) (type_lift n τ2) *)
(*   | Prod τs => Prod (map (type_lift n) τs) *)
(*   | TForall τ' => TForall (type_lift (N.succ n) τ') *)
(*   | TVar x => if N.ltb x n then TVar x else TVar (x + 1) *)
(*   | IntType => τ *)
(*   end. *)

(* Fixpoint term_subst {I} `{FInt I} (v : VarInd) (body arg : Term) : Term := *)
(*   match body with *)
(*   | Var x => *)
(*     if N.eqb x v *)
(*     then arg *)
(*     else Var x *)
(*   | Fix fix_type arg_type fbody => *)
(*     Fix fix_type arg_type (term_subst (v + 2) fbody (term_lift 0 arg)) *)
(*   | Ann e t => Ann (term_subst v e arg) t *)
(*   | App e1 e2 => App (term_subst v e1 arg) (term_subst v e2 arg) *)
(*   | TAbs e => TAbs (term_subst v e arg) *)
(*   | TApp e t => TApp (term_subst v e arg) t *)
(*   | Tuple es => Tuple (map (fun e => term_subst v e arg) es) *)
(*   | ProjN i e => ProjN i (term_subst v e arg) *)
(*   | Num x => Num x *)
(*   | If0 c e1 e2 => If0 (term_subst v c arg) (term_subst v e1 arg) (term_subst v e2 arg) *)
(*   | Op op e1 e2 => Op op (term_subst v e1 arg) (term_subst v e2 arg) *)
(*   end. *)

(* Lemma type_lift_type_size: *)
(*   forall τ n, *)
(*     type_size (type_lift n τ) = type_size τ. *)
(* Proof. *)
(*   induction τ; intros sz; cbn; *)
(*   repeat match goal with *)
(*     H: _ |- _ => *)
(*     rewrite H *)
(*   end; eauto. *)

(*   destruct (x <? sz)%N; auto. *)

(*   rewrite map_map. *)
(*   erewrite map_ext_in; eauto. *)
(* Qed. *)

(* Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]]. *)
(* Program Fixpoint type_subst_in_type (v : TypeInd) (τ : FType) (arg : FType) {measure (type_size τ)} : FType := *)
(*   match τ with *)
(*   | TVar x => *)
(*     if N.eqb x v *)
(*     then arg *)
(*     else if N.ltb v x *)
(*          then TVar (x-1) *)
(*          else TVar x *)
(*   | Arrow τ1 τ2 => Arrow (type_subst_in_type v τ1 arg) (type_subst_in_type v τ2 arg) *)
(*   | Prod τs => *)
(*     Prod (map_In τs (fun τ HIn => type_subst_in_type v τ arg)) *)
(*   | TForall τ' => TForall (type_subst_in_type (v+1) τ' (type_lift 0 arg)) *)
(*   | IntType => IntType *)
(*   end. *)
(* Next Obligation. *)
(*   cbn. *)
(*   pose proof (list_sum_map type_size τ τs HIn). *)
(*   lia. *)
(* Qed. *)

(* Fixpoint type_subst {I} `{FInt I} (v : TypeInd) (e : Term) (arg_type : FType) : Term *)
(*   := match e with *)
(*      | TAbs e => TAbs (type_subst (v+1) e (type_lift 0 arg_type)) *)
(*      | TApp e τ => TApp (type_subst v e arg_type) (type_subst_in_type v τ arg_type) *)
(*      | Fix fτ τ body => Fix (type_subst_in_type v fτ arg_type) (type_subst_in_type v τ arg_type) (type_subst v body arg_type) *)
(*      | App e1 e2 => App (type_subst v e1 arg_type) (type_subst v e2 arg_type) *)
(*      | If0 c e1 e2 => If0 (type_subst v c arg_type) (type_subst v e1 arg_type) (type_subst v e2 arg_type) *)
(*      | Op op e1 e2 => Op op (type_subst v e1 arg_type) (type_subst v e2 arg_type) *)
(*      | Tuple es => Tuple (map (fun e => type_subst v e arg_type) es) *)
(*      | ProjN i e => ProjN i (type_subst v e arg_type) *)
(*      | Ann e τ => Ann (type_subst v e arg_type) (type_subst_in_type v τ arg_type) *)
(*      | Num x => Num x *)
(*      | Var x => Var x *)
(*      end. *)

(* Definition eval_primop {I} `{FInt I} (op : PrimOp) : (I -> I -> I) := *)
(*   match op with *)
(*   | Mul => mul *)
(*   | Add => add *)
(*   | Sub => sub *)
(*   end. *)

(* Definition eval_op {I} `{FInt I} (op : PrimOp) (x y : I) : I := *)
(*   eval_primop op x y. *)

(* Definition app_fix {I} `{FInt I} (fix_type arg_type : FType) (body : Term) (arg : Term) : Term := *)
(*   term_subst 1 (term_subst 0 body (Fix fix_type arg_type body)) arg. *)

(* Fixpoint zipwith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z *)
(*   := match xs, ys with *)
(*      | (x :: xs), (y :: ys) => f x y :: (zipwith f xs ys) *)
(*      | _, _ => nil *)
(*      end. *)


(* Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]]. *)
(* Program Fixpoint step {I} `{FInt I} (e : Term) {measure (term_size e)} : (unit + Term) := *)
(*   match e with *)
(*   | Ann e t => step e *)
(*   | Fix fix_type arg_type body => inl tt *)
(*   | App (Fix fix_type arg_type body) arg => *)
(*     inr (app_fix fix_type arg_type body arg) *)
(*   | App e1 e2 => *)
(*     e1v <- step e1;; *)
(*     inr (App e1v e2) *)
(*   | Op op (Num xn) (Num yn) => *)
(*     inr (Num (eval_op op xn yn)) *)
(*   | Op op (Num xn) y => *)
(*     yv <- step y ;; *)
(*     inr (Op op (Num xn) yv) *)
(*   | Op op x y => *)
(*     xv <- step x ;; *)
(*     inr (Op op xv y) *)
(*   | TApp (TAbs e) arg_type => *)
(*     inr (type_subst 0 e arg_type) *)
(*   | TApp e t => *)
(*     e' <- step e;; *)
(*     inr (TApp e' t) *)
(*   | ProjN i (Tuple es) => *)
(*     match nth_error es (N.to_nat i) with *)
(*     | Some e => step e *)
(*     | None => inl tt *)
(*     end *)
(*   | ProjN i e => *)
(*     ev <- step e;; *)
(*     inr (ProjN i ev) *)
(*   | If0 (Num x) e1 e2 => *)
(*     if eq x zero *)
(*     then inr e1 *)
(*     else inr e2 *)
(*   | If0 c e1 e2 => *)
(*     cv <- step c;; *)
(*     inr (If0 cv e1 e2) *)
(*   | _ => inl tt *)
(*   end. *)
(* Next Obligation. *)
(*   cbn. *)
(*   symmetry in Heq_anonymous. *)
(*   apply nth_error_In in Heq_anonymous. *)
(*   pose proof (list_sum_map term_size e es Heq_anonymous). *)
(*   lia. *)
(* Qed. *)

(* Fixpoint zip_pred {X Y} (pred : X -> Y -> bool) (xs : list X) (ys : list Y) : bool *)
(*   := match xs, ys with *)
(*      | nil, nil => true *)
(*      | x::xs, y::ys => pred x y && zip_pred pred xs ys *)
(*      | _, _ => false *)
(*      end. *)

(* Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate | intros; intros CONTRA; inv CONTRA; discriminate]]. *)
(* Program Fixpoint ftype_eq (τ1 : FType) (τ2 : FType) {measure (type_size τ1 + type_size τ2)} : bool *)
(*   := match τ1, τ2 with *)
(*      | Arrow a1 b1, Arrow a2 b2 => ftype_eq a1 a2 && ftype_eq b1 b2 *)
(*      | Prod es1, Prod es2 => *)
(*        zip_pred (fun τ1 τ2 => ftype_eq τ1 τ2) es1 es2 *)
(*      | TForall t1, TForall t2 => ftype_eq t1 t2 *)
(*      | TVar x, TVar y => N.eqb x y *)
(*      | IntType, IntType => true *)
(*      | _, _ => false *)
(*      end. *)
(* Next Obligation. *)
(* Admitted. *)

(* Definition op_eq (op1 op2 : PrimOp) : bool *)
(*   := match op1, op2 with *)
(*      | Mul, Mul => true *)
(*      | Add, Add => true *)
(*      | Sub, Sub => true *)
(*      | _, _ => false *)
(*      end. *)

(* Program Fixpoint term_eq (e1 e2 : Term) {measure (term_size e1 + term_size e2)} : bool *)
(*   := match e1, e2 with *)
(*      | Var x, Var y => N.eqb x y *)
(*      | Ann e1 t1, Ann e2 t2 => term_eq e1 e2 && ftype_eq t1 t2 *)
(*      | Fix fτ1 aτ1 body1, Fix fτ2 aτ2 body2 => *)
(*        ftype_eq fτ1 fτ2 && ftype_eq aτ1 aτ2 && term_eq body1 body2 *)
(*      | App f1 a1, App f2 a2 => *)
(*        term_eq f1 f2 && term_eq a1 a2 *)
(*      | TAbs x, TAbs y => term_eq x y *)
(*      | TApp e1 τ1, TApp e2 τ2 => term_eq e1 e2 && ftype_eq τ1 τ2 *)
(*      | Tuple xs, Tuple ys => *)
(*        zip_pred (fun e1 e2 => term_eq e1 e2) xs ys *)
(*      | ProjN i1 e1, ProjN i2 e2 => *)
(*        N.eqb i1 i2 && term_eq e1 e2 *)
(*      | Num x, Num y => eq x y *)
(*      | If0 c1 a1 b1, If0 c2 a2 b2 => *)
(*        term_eq c1 c2 && term_eq a1 a2 && term_eq b1 b2 *)
(*      | Op op1 a1 b1, Op op2 a2 b2 => *)
(*        op_eq op1 op2 && term_eq a1 a2 && term_eq b1 b2 *)
(*      | _, _ => false *)
(*      end. *)
(* Next Obligation. *)
(*   cbn. *)
(* Admitted. *)

(* Definition Failure := exceptE string. *)
(* Open Scope string_scope. *)

(* Definition eval_body {I} `{FInt I} `{Show I} (e : Term) : itree (callE Term Term +' Failure) Term := *)
(*   match e with *)
(*   | Ann e t => call e *)
(*   | App e1 e2 => *)
(*     e1v <- call e1;; *)
(*     e2v <- call e2;; *)
(*     match e1v with *)
(*     | Fix fix_type arg_type body => *)
(*       call (app_fix fix_type arg_type body e2v) *)
(*     | _ => throw ("ill-typed application: " ++ show e) *)
(*     end *)
(*   | TApp e t => *)
(*     e' <- call e;; *)
(*     match e' with *)
(*     | TAbs body => *)
(*       call (type_subst 0 body t) *)
(*     | _ => throw ("ill-typed type application: " ++ show (TApp e' t)) *)
(*     end *)
(*   | ProjN i es => *)
(*     es' <- call es;; *)
(*     match es' with *)
(*     | Tuple xs => *)
(*       match nth_error xs (N.to_nat i) with *)
(*       | Some e => call e *)
(*       | None => throw ("tuple projection out of bounds: " ++ show e) *)
(*       end *)
(*     | _ => throw ("ill-typed tuple projection: " ++ show e) *)
(*     end *)
(*   | If0 c e1 e2 => *)
(*     cv <- call c;; *)
(*     match cv with *)
(*     | Num x => *)
(*       if eq x zero *)
(*       then call e1 *)
(*       else call e2 *)
(*     | _ => throw ("ill-typed if0: " ++ show e) *)
(*     end *)
(*   | Op op e1 e2 => *)
(*     e1v <- call e1;; *)
(*     e2v <- call e2;; *)
(*     match e1v, e2v with *)
(*     | Num x, Num y => *)
(*       ret (Num (eval_op op x y)) *)
(*     | _, _ => throw ("ill-typed operation: " ++ show e) *)
(*     end *)
(*   | Num x => ret e *)
(*   | TAbs x => ret e *)
(*   | Tuple xs => *)
(*     xs' <- map_monad call xs;; *)
(*     ret (Tuple xs') *)
(*   | Fix fix_type arg_type body => ret e *)
(*   | Var x => ret e *)
(*   end. *)

(* Definition eval {I} `{FInt I} `{Show I} : Term -> itree Failure Term := *)
(*   rec eval_body. *)

(* Fixpoint well_formed_type (ftv : N) (τ : FType) : bool *)
(*   := match τ with *)
(*      | Arrow τ1 τ2 => well_formed_type ftv τ1 && well_formed_type ftv τ2 *)
(*      | Prod τs => forallb (well_formed_type ftv) τs *)
(*      | TForall τ' => well_formed_type (ftv + 1) τ' *)
(*      | TVar x => N.ltb x ftv *)
(*      | IntType => true *)
(*      end. *)

(* Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate | intros; intros CONTRA; inv CONTRA; discriminate]]. *)
(* Program Fixpoint typeof' {I} `{FInt I} (ftv : N) (Γ : list FType) (e : Term) {measure (term_size e)}: option FType := *)
(*   match e with *)
(*   | Var x => nth_error Γ (N.to_nat x) *)
(*   | Ann e τ => *)
(*     τ' <- (typeof' ftv Γ e);; *)
(*     if ftype_eq τ' τ *)
(*     then Some τ *)
(*     else @None FType *)
(*   | Fix fix_τ arg_τ body => *)
(*     if (well_formed_type ftv fix_τ && well_formed_type ftv arg_τ)%bool *)
(*     then τ <- typeof' ftv (fix_τ::arg_τ::Γ) body;; *)
(*          let τ' := (Arrow arg_τ τ) in *)
(*          if ftype_eq fix_τ τ' *)
(*          then Some τ' *)
(*          else @None FType *)
(*     else None *)
(*   | App e1 e2 => *)
(*     τ12 <- typeof' ftv Γ e1;; *)
(*     τ1 <- typeof' ftv Γ e2;; *)
(*     match τ12 with *)
(*     | Arrow τ1' τ2 => *)
(*       if ftype_eq τ1 τ1' *)
(*       then Some τ2 *)
(*       else @None FType *)
(*     | _ => @None FType *)
(*     end *)
(*   | TAbs e => *)
(*     τ <- typeof' (N.succ ftv) (map (type_lift 0) Γ) e;; *)
(*     ret (TForall τ) *)
(*   | TApp e τ => *)
(*     τ2 <- typeof' ftv Γ e;; *)
(*     if well_formed_type ftv τ *)
(*     then match τ2 with *)
(*          | TForall τ2' => Some (type_subst_in_type 0 τ2' τ) *)
(*          | _ => @None FType *)
(*          end *)
(*     else @None FType *)
(*   | Tuple es => *)
(*     es' <- map_monad (fun e => typeof' ftv Γ e) es;; *)
(*     ret (Prod es') *)
(*   | ProjN i (Tuple es) => *)
(*     e <- nth_error es (N.to_nat i);; *)
(*     typeof' ftv Γ e *)
(*   | ProjN _ _ => None *)
(*   | Num x => Some IntType *)
(*   | If0 c e1 e2 => *)
(*     cτ <- typeof' ftv Γ c;; *)
(*     if ftype_eq cτ IntType *)
(*     then e1τ <- typeof' ftv Γ e1;; *)
(*          e2τ <- typeof' ftv Γ e2;; *)
(*          if ftype_eq e1τ e2τ *)
(*          then Some e1τ *)
(*          else @None FType *)
(*     else @None FType *)
(*   | Op op e1 e2 => *)
(*     e1τ <- typeof' ftv Γ e1;; *)
(*     e2τ <- typeof' ftv Γ e2;; *)
(*     if (ftype_eq e1τ IntType && ftype_eq e2τ IntType)%bool *)
(*     then Some e1τ *)
(*     else @None FType *)
(*   end. *)
(* Next Obligation. *)
(* Admitted. *)
(* Next Obligation. *)
(* Admitted. *)

(* Definition typeof {I} `{FInt I} : Term -> option FType := typeof' 0 nil. *)

(* Fixpoint is_value {I} `{FInt I} (e : Term) : bool := *)
(*   match e with *)
(*   | Var x => true *)
(*   | Ann x x0 => false *)
(*   | Fix x x0 x1 => true *)
(*   | App x x0 => false *)
(*   | TAbs x => true *)
(*   | TApp x x0 => false *)
(*   | Tuple xs => *)
(*     forallb is_value xs *)
(*   | ProjN x x0 => false *)
(*   | Num x => true *)
(*   | If0 x x0 x1 => false *)
(*   | Op x x0 x1 => false *)
(*   end. *)
