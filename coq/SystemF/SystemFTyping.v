From Cofq.SystemF Require Import
     SystemFDefinitions
     SystemFUtils
     SystemFSemantics.

From Coq Require Import Lia ssrbool.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

Import MonadNotation.
Local Open Scope monad_scope.

From Vellvm.Utils Require Import Util.

Fixpoint well_formed_type (ftv : N) (τ : FType) : bool
  := match τ with
     | Arrow τ1 τ2 => well_formed_type ftv τ1 && well_formed_type ftv τ2
     | Prod τs => forallb (well_formed_type ftv) τs
     | TForall τ' => well_formed_type (ftv + 1) τ'
     | TVar x => N.ltb x ftv
     | IntType => true
     end.

Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate | intros; intros CONTRA; inversion CONTRA; discriminate]].
Program Fixpoint typeof' {I} `{FInt I} (ftv : N) (Γ : list FType) (e : Term) {measure (term_size e)}: option FType :=
  match e with
  | Var x => nth_error Γ (N.to_nat x)
  | Ann e τ =>
    τ' <- (typeof' ftv Γ e);;
    if ftype_eq τ' τ
    then Some τ
    else @None FType
  | Fix fix_τ arg_τ body =>
    if (well_formed_type ftv fix_τ && well_formed_type ftv arg_τ)%bool
    then τ <- typeof' ftv (fix_τ::arg_τ::Γ) body;;
         let τ' := (Arrow arg_τ τ) in
         if ftype_eq fix_τ τ'
         then Some τ'
         else @None FType
    else None
  | App e1 e2 =>
    τ12 <- typeof' ftv Γ e1;;
    τ1 <- typeof' ftv Γ e2;;
    match τ12 with
    | Arrow τ1' τ2 =>
      if ftype_eq τ1 τ1'
      then Some τ2
      else @None FType
    | _ => @None FType
    end
  | TAbs e =>
    τ <- typeof' (N.succ ftv) (map (type_lift 0) Γ) e;;
    ret (TForall τ)
  | TApp e τ =>
    τ2 <- typeof' ftv Γ e;;
    if well_formed_type ftv τ
    then match τ2 with
         | TForall τ2' => Some (type_subst_in_type 0 τ2' τ)
         | _ => @None FType
         end
    else @None FType
  | Tuple es =>
    es' <- map_monad (fun e => typeof' ftv Γ e) es;;
    ret (Prod es')
  | ProjN i (Tuple es) =>
    e <- nth_error es (N.to_nat i);;
    typeof' ftv Γ e
  | ProjN _ _ => None
  | Num x => Some IntType
  | If0 c e1 e2 =>
    cτ <- typeof' ftv Γ c;;
    if ftype_eq cτ IntType
    then e1τ <- typeof' ftv Γ e1;;
         e2τ <- typeof' ftv Γ e2;;
         if ftype_eq e1τ e2τ
         then Some e1τ
         else @None FType
    else @None FType
  | Op op e1 e2 =>
    e1τ <- typeof' ftv Γ e1;;
    e2τ <- typeof' ftv Γ e2;;
    if (ftype_eq e1τ IntType && ftype_eq e2τ IntType)%bool
    then Some e1τ
    else @None FType
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition typeof {I} `{FInt I} : Term -> option FType := typeof' 0 nil.

(* Check whether a type is closed *)
Fixpoint is_closed' (tc : N) (τ : FType) : bool
  := match τ with
     | Arrow τ1 τ2 => is_closed' tc τ1 && is_closed' tc τ2
     | Prod τs => forallb (is_closed' tc) τs
     | TForall τ => is_closed' (tc+1) τ
     | TVar x => N.ltb x tc
     | IntType => true
     end.

Definition is_closed := is_closed' 0.

Definition well_typed {I} `{FInt I} (e : Term) : bool
  := ssrbool.isSome (typeof e).
