From Cofq.SystemK Require Import
     SystemKDefinitions
     SystemKUtils
     SystemKShow. (* Need show for errors in evaluation *)

From Cofq.Utils Require Import Utils.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import
     Lia
     List.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

Import MonadNotation.
Local Open Scope monad_scope.

From ITree Require Import
     Basics
     ITree
     Interp.Recursion
     Events.Exception.

From Vellvm.Utils Require Import Util.

Section Substitution.
  Definition nat_to_n (n : nat) : N. Admitted.

  (* Lift by 2 because fixpoint has a argument in addition to referring to itself *)
  Fixpoint value_lift {I} `{FInt I} (n : N) (lift_by : N) (value : KValue) : KValue :=
    match value with
    | KAnnotated type raw_value => KAnnotated type (raw_value_lift n lift_by raw_value)
    end
  with raw_value_lift {I} `{FInt I} (n : N) (lift_by : N) (value : KRawValue) : KRawValue :=
    match value with
    | KNum num => KNum num
    | KVar index =>
      if N.ltb index n
      then KVar index
      else KVar (index + lift_by)
    | KFix type_param_count value_params body =>
      KFix type_param_count
           value_params
           (term_lift (n + (nat_to_n (length value_params)) + 1) lift_by body)
    | KTuple values => KTuple (map (value_lift n lift_by) values)
    end
    with term_lift {I} `{FInt I} (n : N) (lift_by : N) (term : KTerm) : KTerm :=
    match term with
    | KLet declaration body =>
      KLet (declaration_lift n lift_by declaration) (term_lift (n + 1) lift_by body)
    | KApp f type_params value_params =>
      KApp (value_lift n lift_by f) type_params (map (value_lift n lift_by) value_params)
    | KIf0 value then_term else_term =>
      KIf0 (value_lift n lift_by value) (term_lift n lift_by then_term) (term_lift n lift_by else_term)
    | KHalt type value => KHalt type (value_lift n lift_by value)
    end
    with declaration_lift {I} `{FInt I} (n : N) (lift_by : N) (declaration : KDeclaration) : KDeclaration :=
    match declaration with
    | KVal value => KVal (value_lift n lift_by value)
    | KProjN i value => KProjN i (value_lift n lift_by value)
    | KOp op value_a value_b => KOp op (value_lift n lift_by value_a) (value_lift n lift_by value_b)
    end.
  (*
  Fixpoint term_lift {I} `{FInt I} (n : N) (term : Term) : Term :=
    match term with
    | Var x =>
      if N.ltb x n
      then Var x
      else Var (x + 2)
    | Ann term' type => Ann (term_lift n term') type
    | Fix fix_type arg_type fbody => Fix fix_type arg_type (term_lift (n+2) fbody)
    | App e1 e2 => App (term_lift n e1) (term_lift n e2)
    | TAbs e => TAbs (term_lift n e)
    | TApp e t => TApp (term_lift n e) t
    | Tuple es => Tuple (map (term_lift n) es)
    | ProjN i es => ProjN i (term_lift n es)
    | Num x => Num x
    | If0 c e1 e2 => If0 (term_lift n c) (term_lift n e1) (term_lift n e2)
    | Op op e1 e2 => Op op (term_lift n e1) (term_lift n e2)
    end.
    *)

  Fixpoint type_lift (n lift_by : N) (τ : KType) : KType :=
    match τ with
    | KProd types => KProd (map (type_lift n lift_by) types)
    | KTForall type_param_count term_params =>
      KTForall type_param_count (map (type_lift (n + type_param_count) lift_by ) term_params)
    | KTVar index =>
      if N.ltb index n
      then KTVar index
      else KTVar (index + lift_by)
    | KIntType => KIntType
    end.

  Fixpoint term_subst {I} `{FInt I} (v : VarInd) (body arg : Term) : Term :=
    match body with
    | Var x =>
      if N.eqb x v
      then arg
      else Var x
    | Fix fix_type arg_type fbody =>
      Fix fix_type arg_type (term_subst (v + 2) fbody (term_lift 0 arg))
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

  Lemma type_lift_type_size:
    forall τ n,
      type_size (type_lift n τ) = type_size τ.
  Proof.
    induction τ; intros sz; cbn;
      repeat match goal with
               H: _ |- _ =>
               rewrite H
             end; eauto.

    destruct (x <? sz)%N; auto.

    rewrite map_map.
    erewrite map_ext_in; eauto.
  Qed.


  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]].
  Program Fixpoint type_subst_in_type (v : TypeInd) (τ : FType) (arg : FType) {measure (type_size τ)} : FType :=
    match τ with
    | TVar x =>
      if N.eqb x v
      then arg
      else if N.ltb v x
           then TVar (x-1)
           else TVar x
    | Arrow τ1 τ2 => Arrow (type_subst_in_type v τ1 arg) (type_subst_in_type v τ2 arg)
    | Prod τs =>
      Prod (map_In τs (fun τ HIn => type_subst_in_type v τ arg))
    | TForall τ' => TForall (type_subst_in_type (v+1) τ' (type_lift 0 arg))
    | IntType => IntType
    end.
  Next Obligation.
    cbn.
    pose proof (list_sum_map type_size τ τs HIn).
    lia.
  Qed.

  Fixpoint type_subst {I} `{FInt I} (v : TypeInd) (e : Term) (arg_type : FType) : Term
    := match e with
       | TAbs e => TAbs (type_subst (v+1) e (type_lift 0 arg_type))
       | TApp e τ => TApp (type_subst v e arg_type) (type_subst_in_type v τ arg_type)
       | Fix fτ τ body => Fix (type_subst_in_type v fτ arg_type) (type_subst_in_type v τ arg_type) (type_subst v body arg_type)
       | App e1 e2 => App (type_subst v e1 arg_type) (type_subst v e2 arg_type)
       | If0 c e1 e2 => If0 (type_subst v c arg_type) (type_subst v e1 arg_type) (type_subst v e2 arg_type)
       | Op op e1 e2 => Op op (type_subst v e1 arg_type) (type_subst v e2 arg_type)
       | Tuple es => Tuple (map (fun e => type_subst v e arg_type) es)
       | ProjN i e => ProjN i (type_subst v e arg_type)
       | Ann e τ => Ann (type_subst v e arg_type) (type_subst_in_type v τ arg_type)
       | Num x => Num x
       | Var x => Var x
       end.

  Definition app_fix {I} `{FInt I} (fix_type arg_type : FType) (body : Term) (arg : Term) : Term :=
    term_subst 1 (term_subst 0 body (Fix fix_type arg_type body)) arg.
End Substitution.


(** Single-step semantics for SystemF, useful for testing. *)
Section SingleStep.
  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]].
  Program Fixpoint step {I} `{FInt I} (e : Term) {measure (term_size e)} : (unit + Term) :=
    match e with
    | Ann e t => step e
    | Fix fix_type arg_type body => inl tt
    | App (Fix fix_type arg_type body) arg =>
      inr (app_fix fix_type arg_type body arg)
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
    | TApp (TAbs e) arg_type =>
      inr (type_subst 0 e arg_type)
    | TApp e t =>
      e' <- step e;;
      inr (TApp e' t)
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

  Definition step' {I} `{FInt I} (v : unit + Term) : (unit + Term)
    := match v with
       | inl tt => inl tt
       | inr t => step t
       end.

  Fixpoint multistep {I} `{FInt I} (n : nat) (v : Term) : Term
    := match n with
       | O => v
       | S n =>
         match step v with
         | inl tt => v
         | inr t => multistep n t
         end
       end.

  (* Returns a term only if it's fully evaluated *)
  Fixpoint multistep' {I} `{FInt I} (n : nat) (v : Term) : option Term
    := match n with
       | O => None
       | S n =>
         match step v with
         | inl tt => Some v
         | inr t => multistep' n t
         end
       end.
End SingleStep.

(** Denotation of SystemF in terms of itrees. *) 
Section Denotation.
  Definition Failure := exceptE string.

  Definition eval_body {I} `{FInt I} `{Show I} (e : Term) : itree (callE Term Term +' Failure) Term :=
    match e with
    | Ann e t => call e
    | App e1 e2 =>
      e1v <- call e1;;
      e2v <- call e2;;
      match e1v with
      | Fix fix_type arg_type body =>
        call (app_fix fix_type arg_type body e2v)
      | _ => throw ("ill-typed application: " ++ show e)
      end
    | TApp e t =>
      e' <- call e;;
      match e' with
      | TAbs body =>
        call (type_subst 0 body t)
      | _ => throw ("ill-typed type application: " ++ show (TApp e' t))
      end
    | ProjN i es =>
      es' <- call es;;
      match es' with
      | Tuple xs =>
        match nth_error xs (N.to_nat i) with
        | Some e => call e
        | None => throw ("tuple projection out of bounds: " ++ show e)
        end
      | _ => throw ("ill-typed tuple projection: " ++ show e)
      end
    | If0 c e1 e2 =>
      cv <- call c;;
      match cv with
      | Num x =>
        if eq x zero
        then call e1
        else call e2
      | _ => throw ("ill-typed if0: " ++ show e)
      end
    | Op op e1 e2 =>
      e1v <- call e1;;
      e2v <- call e2;;
      match e1v, e2v with
      | Num x, Num y =>
        ret (Num (eval_op op x y))
      | _, _ => throw ("ill-typed operation: " ++ show e)
      end
    | Num x => ret e
    | TAbs x => ret e
    | Tuple xs =>
      xs' <- map_monad call xs;;
      ret (Tuple xs')
    | Fix fix_type arg_type body => ret e
    | Var x => ret e
    end.

  Definition eval {I} `{FInt I} `{Show I} : Term -> itree Failure Term :=
    rec eval_body.
End Denotation.
