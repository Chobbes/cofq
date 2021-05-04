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
  Fixpoint kvalue_lift {I} `{FInt I} (n : N) (lift_by : N) (value : KValue) : KValue :=
    match value with
    | KAnnotated type raw_value => KAnnotated type (kraw_value_lift n lift_by raw_value)
    end
  with kraw_value_lift {I} `{FInt I} (n : N) (lift_by : N) (value : KRawValue) : KRawValue :=
    match value with
    | KNum num => KNum num
    | KVar index =>
      if N.ltb index n
      then KVar index
      else KVar (index + lift_by)
    | KFix type_param_count value_params body =>
      KFix type_param_count
           value_params
           (kterm_lift (n + (nat_to_n (length value_params)) + 1) lift_by body)
    | KTuple values => KTuple (map (kvalue_lift n lift_by) values)
    end
    with kterm_lift {I} `{FInt I} (n : N) (lift_by : N) (term : KTerm) : KTerm :=
    match term with
    | KLet declaration body =>
      KLet (kdeclaration_lift n lift_by declaration) (kterm_lift (n + 1) lift_by body)
    | KApp f type_params value_params =>
      KApp (kvalue_lift n lift_by f) type_params (map (kvalue_lift n lift_by) value_params)
    | KIf0 value then_term else_term =>
      KIf0 (kvalue_lift n lift_by value) (kterm_lift n lift_by then_term) (kterm_lift n lift_by else_term)
    | KHalt type value => KHalt type (kvalue_lift n lift_by value)
    end
    with kdeclaration_lift {I} `{FInt I} (n : N) (lift_by : N) (declaration : KDeclaration) : KDeclaration :=
    match declaration with
    | KVal value => KVal (kvalue_lift n lift_by value)
    | KProjN i value => KProjN i (kvalue_lift n lift_by value)
    | KOp op value_a value_b => KOp op (kvalue_lift n lift_by value_a) (kvalue_lift n lift_by value_b)
    end.

  Fixpoint ktype_lift (n lift_by : N) (τ : KType) : KType :=
    match τ with
    | KProd types => KProd (map (ktype_lift n lift_by) types)
    | KTForall type_param_count term_params =>
      KTForall type_param_count (map (ktype_lift (n + type_param_count) lift_by) term_params)
    | KTVar index =>
      if N.ltb index n
      then KTVar index
      else KTVar (index + lift_by)
    | KIntType => KIntType
    end.
  
  Fixpoint kvalue_subst {I} `{FInt I} (v : VarInd) (body : KValue) (arg : KRawValue) : KValue :=
    match body with
    | KAnnotated type raw_value => KAnnotated type (kraw_value_subst v raw_value arg)
    end
  with kraw_value_subst {I} `{FInt I} (v : VarInd) (body : KRawValue) (arg : KRawValue) : KRawValue :=
    match body with
    | KNum num => KNum num
    | KVar index =>
      if N.eqb index v
      then arg
      else KVar index
    | KFix type_param_count value_params fbody =>
      KFix type_param_count
          value_params
          (kterm_subst
            (v + (nat_to_n (length value_params)) + 1)
            fbody
            (kraw_value_lift 0 ((nat_to_n (length value_params)) + 1) arg)
          )
    | KTuple tuple_bodies => KTuple (map (fun tuple_body => kvalue_subst v tuple_body arg) tuple_bodies)
    end
    with kterm_subst {I} `{FInt I} (v : VarInd) (body : KTerm) (arg : KRawValue) : KTerm :=
      match body with
      | KLet declaration lbody =>
        KLet
          (kdeclaration_subst v declaration arg)
          (kterm_subst
            (v + 1)
            lbody
            (kraw_value_lift 0 1 arg)
          )
      | KApp f type_params value_params =>
        KApp
          (kvalue_subst v f arg)
          type_params
          (map (fun value_param => kvalue_subst v value_param arg) value_params)
      | KIf0 value then_term else_term =>
        KIf0
          (kvalue_subst v value arg)
          (kterm_subst v then_term arg)
          (kterm_subst v else_term arg)
      | KHalt type value =>
        KHalt type (kvalue_subst v value arg)
      end
    with kdeclaration_subst {I} `{FInt I} (v : VarInd) (body : KDeclaration) (arg : KRawValue) : KDeclaration :=
      match body with
      | KVal value =>
        KVal (kvalue_subst v value arg) 
      | KProjN i value =>
        KProjN i (kvalue_subst v value arg) 
      | KOp op value_a value_b =>
        KOp op
          (kvalue_subst v value_a arg)
          (kvalue_subst v value_b arg)
      end
    .

  (*
  Lemma type_lift_type_size:
    forall τ n,
      type_size (ktype_lift n τ) = type_size τ.
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
  *)

  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]].
  Program Fixpoint ktype_subst_in_type (v : TypeInd) (τ : KType) (arg : KType) {measure (ktype_size τ)} : KType :=
    match τ with
    | KProd τs =>
      KProd (map_In τs (fun τ HIn => ktype_subst_in_type v τ arg))
    | KTForall type_param_count term_params =>
      KTForall type_param_count
               (map_In term_params
                       (fun τ' HIn => ktype_subst_in_type (v + type_param_count) τ' (ktype_lift 0 type_param_count arg)))
    | KTVar x =>
      if N.eqb x v
      then arg
      else if N.ltb v x
          then KTVar (x-1)
          else KTVar x
    | KIntType => KIntType
    end.
  Next Obligation.
    cbn.
    pose proof (list_sum_map ktype_size τ τs HIn).
    lia.
  Qed.
  Next Obligation.
    cbn.
    pose proof (list_sum_map ktype_size τ' term_params HIn).
    lia.
  Qed.

  Fixpoint ktype_subst_value {I} `{FInt I} (v : TypeInd) (e : KValue) (arg_type : KType) : KValue :=
    match e with
    | KAnnotated type raw_value =>
      KAnnotated
        (ktype_subst_in_type v type arg_type)
        (ktype_subst_raw_value v raw_value arg_type)
    end
  with ktype_subst_raw_value {I} `{FInt I} (v : TypeInd) (e : KRawValue) (arg_type : KType) : KRawValue :=
    match e with
    | KNum num => KNum num
    | KVar index => KVar index
    | KFix type_param_count value_params fbody =>
      KFix type_param_count
        (map (fun value_param => ktype_subst_in_type (v + type_param_count) value_param arg_type) value_params)
        (ktype_subst_term (v + type_param_count) fbody arg_type)
    | KTuple tuple_bodies => 
      KTuple (map (fun tuple_body => ktype_subst_value v tuple_body arg_type) tuple_bodies)
    end
  with ktype_subst_term {I} `{FInt I} (v : TypeInd) (e : KTerm) (arg_type : KType) : KTerm :=
    match e with
    | KLet declaration lbody =>
      KLet
        (ktype_subst_declaration v declaration arg_type)
        (ktype_subst_term v lbody arg_type)
    | KApp f type_params value_params =>
      KApp
        (ktype_subst_value v f arg_type)
        (map (fun type => ktype_subst_in_type v type arg_type) type_params)
        (map (fun value => ktype_subst_value v value arg_type) value_params)
    | KIf0 value then_term else_term =>
      KIf0
        (ktype_subst_value v value arg_type)
        (ktype_subst_term v then_term arg_type)
        (ktype_subst_term v else_term arg_type)
    | KHalt type value =>
      KHalt
        (ktype_subst_in_type v type arg_type)
        (ktype_subst_value v value arg_type)
    end
  with ktype_subst_declaration {I} `{FInt I} (v : TypeInd) (e : KDeclaration) (arg_type : KType) : KDeclaration :=
    match e with
    | KVal value => KVal (ktype_subst_value v value arg_type)
    | KProjN i value => KProjN i (ktype_subst_value v value arg_type)
    | KOp op value_a value_b =>
      KOp op
        (ktype_subst_value v value_a arg_type)
        (ktype_subst_value v value_b arg_type)
    end
  .

  Fixpoint type_subst {I} `{FInt I} (v : TypeInd) (e : Term) (arg_type : FType) : Term
    := match e with
       | TAbs e => TAbs (type_subst (v+1) e (ktype_lift 0 arg_type))
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
    kterm_subst 1 (kterm_subst 0 body (Fix fix_type arg_type body)) arg.
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
