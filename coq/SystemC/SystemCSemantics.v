From Cofq.SystemC Require Import
     SystemCDefinitions
     SystemCShow (* Need show for errors in evaluation *)
     SystemCUtils.

From Cofq.Utils Require Import Utils.
From Cofq.BaseExpressions Require Import Integers.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import
     List
     Lia
     ZArith.

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

  Fixpoint cterm_lift_raw_value {I} `{FInt I} (lift_amt : N) (n : N) (rv : CRawValue) : CRawValue :=
    match rv with
    | CNum x => CNum x
    | CVar x =>
      if N.ltb x n
      then CVar x
      else CVar (x + lift_amt)
    | CTuple es => CTuple (map (cterm_lift_value lift_amt n) es)
    | CPack t1 rv t2 => CPack t1 (cterm_lift_raw_value lift_amt n rv) t2
    end
  with
  cterm_lift_value {I} `{FInt I} (lift_amt : N) (n : N) (v : CValue) : CValue :=
    match v with
    | CAnnotated rv t => CAnnotated (cterm_lift_raw_value lift_amt n rv) t
    end.

  Definition cterm_lift_declaration {I} `{FInt I} (lift_amt : N) (n : N) (dec : CDeclaration) : CDeclaration :=
    (* TODO: lift by varied amount for declarations. E.g, unpack binds value and type? *)
    match dec with
    | CVal v => CVal (cterm_lift_value lift_amt n v)
    | CProjN i v => CProjN i (cterm_lift_value lift_amt n v)
    | COp op v1 v2 => COp op (cterm_lift_value lift_amt n v1) (cterm_lift_value lift_amt n v2)
    | CUnpack rv => CUnpack (cterm_lift_raw_value lift_amt n rv)
    end.

  Fixpoint cterm_lift_term {I} `{FInt I} (lift_amt : N) (n : N) (term : CTerm) : CTerm :=
    match term with
    (* Let should always bind a single term variable *)
    | CLet d e => CLet (cterm_lift_declaration lift_amt n d) (cterm_lift_term lift_amt (n+1) e)
    | CApp v targs args => CApp (cterm_lift_value lift_amt n v) targs (map (cterm_lift_value lift_amt n) args)
    | CIf0 c e1 e2 => CIf0 (cterm_lift_value lift_amt n c) (cterm_lift_term lift_amt n e2) (cterm_lift_term lift_amt n e2)
    | CHalt v t => CHalt (cterm_lift_value lift_amt n v) t
    end.

  Definition cterm_lift_heap_value {I} `{FInt I} (lift_amt : N) (n : N) (hv : CHeapValue) : CHeapValue :=
    match hv with
    | CCode t n ts body => CCode t n ts (cterm_lift_term lift_amt n body)
    end.

  (* Each heap value in the list is bound to a type variable in order *)
  Definition CProgram {I} `{FInt I} (lift_amt : N) (n : N) (prog : CProgram) : CProgram :=
    match prog with
    | CProg hvs =>
      CProg (map (fun '(i, hv) => cterm_lift_heap_value lift_amt (n+i) hv) (addIndices hvs))
    end.

  Fixpoint ctype_lift (lift_amt : N) (n : N) (τ : CType) : CType :=
    match τ with
    | CTForall n_type_bindings arrows => CTForall n_type_bindings (map (ctype_lift lift_amt (n + n_type_bindings)) arrows)
    | CTExists τ => CTExists (ctype_lift lift_amt (n + 1) τ)
    | CProd τs => CProd (map (ctype_lift lift_amt n) τs)
    | CTVar x =>
      if N.ltb x n then CTVar x else CTVar (x + lift_amt)
    | CIntType => τ
    end.

  (** * Actual substitution *)

  (* Applications must be a code block applied using the CApp
     constructor to some CType and CValue arguments.

     CApp : CValue -> list CType -> list CValue -> CTerm

     Which means that the code block has to be referenced through an
     annotated CVar, as there's no other way to reference code in a
     value.

     The body of CCode is a term, so we'll have to be able to
     substitute values and types into terms.
   *)

  Fixpoint cterm_subst_raw_value {I} `{FInt I} (v : VarInd) (body arg : CRawValue) : CRawValue :=
    match body with
    | CVar x =>
      if N.eqb x v
      then arg
      else CVar x
    | CNum x => CNum x
    | CTuple es => CTuple (map (fun e => cterm_subst_value v e arg) es)
    | CPack t1 rv t2 => CPack t1 (cterm_subst_raw_value v rv arg) t2
    end
  with
  cterm_subst_value {I} `{FInt I} (v : VarInd) (body : CValue) (arg : CRawValue) : CValue :=
    match body with
    | CAnnotated rv t => CAnnotated (cterm_subst_raw_value v rv arg) t
    end.

  Definition cterm_subst_declaration {I} `{FInt I} (v : VarInd) (body : CDeclaration) (arg : CRawValue) : CDeclaration :=
    match body with
    | CVal val => CVal (cterm_subst_value v val arg)
    | CProjN i val => CProjN i (cterm_subst_value v val arg)
    | COp op v1 v2 => COp op (cterm_subst_value v v1 arg) (cterm_subst_value v v2 arg)
    | CUnpack x => CUnpack (cterm_subst_raw_value v x arg)
    end.

  Fixpoint cterm_subst_term {I} `{FInt I} (v : VarInd) (body : CTerm) (arg : CRawValue) : CTerm :=
    match body with
    | CLet dec e => (* Need to lift here *)
      CLet (cterm_subst_declaration v dec arg) (cterm_subst_term (v+1) e arg)
    | CApp f τs es =>
      CApp (cterm_subst_value v f arg) τs (map (fun e => cterm_subst_value v e arg) es)
    | CIf0 c e1 e2 =>
      CIf0 (cterm_subst_value v c arg)
           (cterm_subst_term v e1 arg)
           (cterm_subst_term v e2 arg)
    | CHalt x τ =>
      CHalt (cterm_subst_value v x arg) τ
    end.

  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | repeat split; try solve [intros; discriminate]].
  Program Fixpoint type_subst_in_type (v : TypeInd) (τ : CType) (arg : CType) {measure (ctype_size τ)} : CType :=
    match τ with
    | CTVar x =>
      if N.eqb x v
      then arg
      else if N.ltb v x
           then CTVar (x-1)
           else CTVar x
    | CProd τs =>
      CProd (map_In τs (fun τ HIn => type_subst_in_type v τ arg))
    | CTForall n τs => CTForall n (map (fun τ => type_subst_in_type (v+n) τ (ctype_lift 1 0 arg)) τs)
    | CTExists τ => CTExists (type_subst_in_type (v+1) τ (ctype_lift 1 0 arg))
    | CIntType => CIntType
    end.
  Next Obligation.
    cbn.
    pose proof (list_sum_map ctype_size τ τs HIn).
    lia.
  Qed.

  Definition ctype_subst_declaration {I} `{FInt I} (v : TypeInd) (e : CDeclaration) (arg_type : CType) : CDeclaration
    := match e with
       | CVal x => 
       | CProjN x x0 => _
       | COp x x0 x1 => _
       | CUnpack x => _
       end
  
  Fixpoint ctype_subst_term {I} `{FInt I} (v : TypeInd) (e : CTerm) (arg_type : CType) : CTerm
    := match e with
       | CLet dec e => CLet (ctype_subst
       | CApp x x0 x1 => _
       | CIf0 x x0 x1 => _
       | CHalt x x0 => _
       end



      match e with
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
