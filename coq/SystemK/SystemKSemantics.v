From Cofq.SystemK Require Import
     SystemKDefinitions
     SystemKUtils
     SystemKShow. (* Need show for errors in evaluation *)

From Cofq.Utils Require Import Utils.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import
     Lia
     String
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
           (kterm_lift (n + (N.of_nat (length value_params)) + 1) lift_by body)
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
            (v + (N.of_nat (length value_params)) + 1)
            fbody
            (kraw_value_lift 0 ((N.of_nat (length value_params)) + 1) arg)
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
End Substitution.

(** Denotation of SystemK in terms of itrees. *) 
Section Denotation.
Set Implicit Arguments.
Set Contextual Implicit.
  Definition Failure := exceptE string.

  Definition kv_to_rv {I} `{FInt I} (val : KValue) : KRawValue
    := match val with
       | KAnnotated τ rv => rv
       end.

  Open Scope string_scope.
  Definition keval_declaration {I} `{FInt I} (*`{Show I}*) (dec : KDeclaration) : itree Failure ((KType * KRawValue) + KRawValue)
    := match dec with
       | KVal x =>
         ret (inr (kv_to_rv x))
       | KProjN i v =>
         match kv_to_rv v with
         | KTuple vs =>
           match nth_error vs (N.to_nat i) with
           | Some e => ret (inr (kv_to_rv e))
           | None => throw ("Tuple projection out of bounds: "(* ++ show dec*))
           end
         | _ =>
           throw ("Ill-typed projection: "(* ++ show dec*))
         end
       | KOp op e1 e2 =>
         match kv_to_rv e1, kv_to_rv e2 with
         | KNum x, KNum y =>
           ret (inr (KNum (eval_op op x y)))
         | _, _ =>
           throw ("Ill-typed operation: "(* ++ show dec*))
         end
       end.

  Notation TermE := (callE KTerm KRawValue +' Failure).
  Notation ProgE := Failure.

  Definition fail_to_TermE {I} `{FInt I} : Failure ~> TermE :=
    fun T f => inr1 f.

  Definition keval_declaration' {I} `{FInt I} `{Show I} (dec : KDeclaration) : itree TermE ((KType * KRawValue) + KRawValue) :=
    translate fail_to_TermE (keval_declaration dec).
  
  Definition apply_args {I} `{FInt I} (e : KTerm) (args : list KValue) : KTerm
    := fold_left (fun body '(i, arg) => kterm_subst i body (kv_to_rv arg)) (addIndices' 1 args) e.

  Definition apply_type_args {I} `{FInt I} (e : KTerm) (type_args : list KType) : KTerm
  := fold_left (fun body '(i, type_arg) => ktype_subst_term i body type_arg) (addIndices' 1 type_args) e.

  Definition eval_app {I} `{FInt I} (e : KTerm) (x : VarInd) (args : list KValue) : itree TermE KRawValue
    := let body := kterm_subst 0 e (KVar x)
       in call (apply_args body args).

  Definition eval_app_type {I} `{FInt I} (e : KTerm) (x : VarInd) (τ : KType) (args : list KValue) : itree TermE KRawValue
    := let body := kterm_subst 0 (ktype_subst_term 0 e τ) (KVar x)
       in call (apply_args body args).

  Definition raise {E} {A} `{Failure -< E} (msg : string) : itree E A :=
    v <- trigger (Throw msg);; match v: void with end.

  Definition keval_term {I} `{FI: FInt I} `{Show I} (e : KTerm) : itree TermE KRawValue
    := match e with
       | KHalt τ v =>
         ret (kv_to_rv v)
       | KLet dec body =>
         d <- keval_declaration' dec;;
         match d with
         | inl (τ, dv) =>
           call (ktype_subst_term 0 (kterm_subst 0 body dv) τ)
         | inr dv =>
           call (kterm_subst 0 body dv)
         end
       | KApp f type_args args =>
         match kv_to_rv f with
         | KFix n_type_params term_param_types body =>
          let type_substd := apply_type_args body type_args in
          let value_substd := apply_args type_substd args in 
          call (value_substd)
         | KVar x => raise "ILL TYPED APPLICATION ACCORDING TO CALVIN"
         | _ => raise "unimplemented"
         end
       | KIf0 c e1 e2 =>
         match kv_to_rv c with
         | KNum x =>
           if eq x zero
           then call e1
           else call e2
         | _ =>
           raise ("Conditional not a number: "(* ++ show e*))
         end
        
       end.

  Definition keval_term_loop {I} `{FI: FInt I} `{Show I} (e : KTerm) : itree Failure KRawValue
    := rec keval_term e.
End Denotation.