From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

From Coq Require Import
     ZArith
     String
     List.

From Vellvm Require Import
     Numeric.Integers
     Utils.Util.

From Cofq.SystemF Require Import
     SystemFDefinitions
     SystemFSemantics
     SystemFTyping
     SystemFUtils
     SystemFShow.

From Cofq.Utils Require Import
     Utils.

From Cofq.BaseExpressions Require Import
     IntegersShow
     BaseExpressionTests.

From Cofq.Test Require Import TestUtils.

Require Import Lia.

From ExtLib Require Import
     Structures.Monads
     Structures.MonadZero
     Structures.Functor
     Eqv.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

Section Generators.
  Program Fixpoint genFType' (ftv : nat) (sz : nat) {measure sz} : G FType
    := match sz with
       | O => elems_fail (IntType :: map TVar (map N.of_nat (seq 0 ftv)))
       | S n' =>
         oneOf_ failGen
                [ genFType' ftv 0;
                a <- genFType' ftv (sz / 6);; b <- genFType' ftv (sz / 4);; ret (Arrow a b);
                a <- genFType' (S ftv) (sz - 1);; ret (TForall a);
                ts <- listOf (genFType' ftv (sz / 2));; ret (Prod ts)
                ]
       end.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Definition genFType (ftv : nat) : G FType
    := sized (genFType' ftv).

  Definition genIfType {A} (τ1 τ2 : FType) (g : G A) : list (G A)
    := if ftype_eq τ1 τ2 then [g] else [].

  (* Randomly fetch a subterm of a type *)
  Fixpoint fetch_sub_type (τ : FType) : G FType
    :=
      oneOf_ failGen
             ((assert (is_closed τ);; [returnGen τ]) ++
                                                    (match τ with
                                                     | Arrow τ1 τ2 => [fetch_sub_type τ1 ; fetch_sub_type τ2]
                                                     | Prod τs => map fetch_sub_type τs
                                                     | TForall τ => [fetch_sub_type τ]
                                                     | _ => []
                                                     end)).

  (* Replace (some occurrences of) closed type s in type t by (TVar n) *)
  Fixpoint replace_sub_type (n : VarInd) (τ arg_τ : FType) : G FType
    := oneOf_ failGen
              ([ returnGen τ ] ++
                               (assert (ftype_eq τ arg_τ);; [returnGen (TVar n)]) ++
                               match τ with
                               | Arrow τ1 τ2 =>
                                 [τ1' <- replace_sub_type n τ1 arg_τ;;
                                  τ2' <- replace_sub_type n τ2 arg_τ;;
                                  returnGen (Arrow τ1' τ2')
                                 ]
                               | Prod τs =>
                                 [τs' <- map_monad (fun τ => replace_sub_type n τ arg_τ) τs;;
                                  returnGen (Prod τs)
                                 ]
                               | TForall τ =>
                                 (* TODO: make sure this is right *)
                                 assert (ftype_eq τ arg_τ);;
                                 [τ' <- replace_sub_type (n+1) τ arg_τ;;
                                  returnGen (TForall τ')
                                 ]
                               | _ => []
                               end).

  (* Generate t1 t2 such that t1{0:=t2} = t *)
  Definition genT1T2 (τ : FType) : G (FType * FType)
    := let τ' := type_lift 0 τ
       in τ2 <- fetch_sub_type τ';;
          (* τ1 <- replace_sub_type 0 τ' τ2;; *)
          returnGen (TForall τ', τ2).

  (* Probably want a variant of this that won't make recursive calls *)
  Program Fixpoint genTerm' (ftv : nat) (Γ : list FType) (τ : FType) (sz : nat) {measure sz} : G Term
    :=
      match sz with
      | 0 =>
        oneOf_ failGen
               ( (assert (ftype_eq IntType τ);; ret (fmap Num genInt64)) ++
                                                                        (* Generate variables from the context with the same type *)
                                                                        ('(i,τ') <- addIndices Γ;; assert (ftype_eq τ' τ);; ret (returnGen (Var i))) ++
                                                                        (* Generate fixpoints... Need a way of ruling out recursive applications *)
                                                                        (match τ with
                                                                         | Arrow τ1 τ2 =>
                                                                           [arg <- genTerm' ftv ((Arrow τ1 τ2) :: τ1 :: Γ) τ2 0;;
                                                                            returnGen (Fix (Arrow τ1 τ2) τ1 arg)
                                                                           ]
                                                                         | TForall τ1 =>
                                                                           [e <- genTerm' (ftv+1) (map (type_lift 0) Γ) τ1 0;;
                                                                            returnGen (TAbs e)
                                                                           ]
                                                                         | Prod τs =>
                                                                           [τs' <- map_monad (fun τ => genTerm' ftv Γ τ 0) τs;;
                                                                            returnGen (Tuple τs')
                                                                           ]
                                                                         | _ => []
                                                                         end)
               )
      | S x =>
        cut
          (freq_ failGen
                 ([(6, genTerm' ftv Γ τ 0);
                  (* Applications *)
                  (8, τ2 <- backTrack 2 (resize 10 (genFType ftv));;
                      nr <- choose (1,2);;
                      me1 <- backTrack nr (genTerm' ftv Γ (Arrow τ2 τ) (sz / 2));;
                      me2 <- genTerm' ftv Γ τ2 (sz / 2);;
                      returnGen (App me1 me2));
                  (* Type applications *)
                  (4, '(τ1, τ2) <- genT1T2 τ;;
                      me1 <- genTerm' ftv Γ τ1 (sz - 1);;
                      returnGen (TApp me1 τ2));
                  (* If0 *)
                  (1, c <- genTerm' ftv Γ IntType (sz / 3);;
                      e1 <- genTerm' ftv Γ τ (sz / 3);;
                      e2 <- genTerm' ftv Γ τ (sz / 3);;
                      returnGen (If0 c e1 e2))
                    (* TODO: unimplemented *)
                    (* Tuple projections *)
                    (* Annotated terms *)
                  ] ++
                    (match τ with
                     | Arrow τ1 τ2 =>
                       [(8, (arg <- genTerm' ftv ((Arrow τ1 τ2) :: τ1 :: Γ) τ2 (sz-1);;
                             returnGen (Fix (Arrow τ1 τ2) τ1 arg)))]
                     | TForall τ1 =>
                       [(4, (e <- genTerm' (ftv+1) (map (type_lift 0) Γ) τ1 (sz-1);;
                             returnGen (TAbs e)))]
                     | Prod τs =>
                       [(1, (τs' <- map_monad (fun τ => genTerm' ftv Γ τ (sz / (length τs))) τs;;
                             returnGen (Tuple τs')))]
                     | IntType =>
                       [(* Operators *)
                         (1, op <- genPrimOp;;
                             e1 <- genTerm' ftv Γ IntType (sz / 2);;
                             e2 <- genTerm' ftv Γ IntType (sz / 2);;
                             returnGen (Op op e1 e2))]
                     | _ => []
                     end)
                 )
          )
      end.
  Admit Obligations.

  Definition genTerm (ftv : nat) (Γ : list FType) (τ : FType) : G Term
    := sized (genTerm' ftv Γ τ).

  (* inl means it's a fixpoint variable *)
  Program Fixpoint genTerm_terminating' (ftv : nat) (Γ : list (FType + FType)) (τ : FType) (sz : nat) {measure sz} : G Term
    :=
      match sz with
      | 0 =>
        oneOf_ failGen
               ( (assert (ftype_eq IntType τ);; ret (fmap Num genInt64)) ++
                                                                        (* Generate variables from the context with the same type *)
                                                                        ('(i,mτ) <- addIndices Γ;; 
                                                                         match mτ with
                                                                         | inr τ' =>
                                                                           assert (ftype_eq τ' τ);; ret (returnGen (Var i))
                                                                         | _ => [] (* Exclude fixpoint variables in general *)
                                                                         end) ++
                                                                        (match τ with
                                                                         | Arrow τ1 τ2 =>
                                                                           [arg <- genTerm_terminating' ftv (inl (Arrow τ1 τ2) :: inr τ1 :: Γ) τ2 0;;
                                                                            returnGen (Fix (Arrow τ1 τ2) τ1 arg)
                                                                           ]
                                                                         | TForall τ1 =>
                                                                           [e <- genTerm_terminating' (ftv+1) (map (map_both (type_lift 0)) Γ) τ1 0;;
                                                                            returnGen (TAbs e)
                                                                           ]
                                                                         | Prod τs =>
                                                                           [τs' <- map_monad (fun τ => genTerm_terminating' ftv Γ τ 0) τs;;
                                                                            returnGen (Tuple τs')
                                                                           ]
                                                                         | _ => []
                                                                         end)
               )
      | S x =>
        cut
          (freq_ failGen
                 ([(6, genTerm_terminating' ftv Γ τ 0);
                  (* Applications *)
                  (8, τ2 <- backTrack 2 (resize 10 (genFType ftv));;
                      nr <- choose (1,2);;
                      me1 <- backTrack nr (genTerm_terminating' ftv Γ (Arrow τ2 τ) (sz / 2));;
                      me2 <- genTerm_terminating' ftv Γ τ2 (sz / 2);;
                      returnGen (App me1 me2));
                  (* Generate simple loops *)
                  (1, loop_count <- choose (1%Z,5%Z);;

                      (* Loop counter *)
                      let loop_start := Num (Int64.repr loop_count) in
                      (* count_dec : IntType *)
                      let count_dec := (Op Sub (Var 1) (Num (Int64.repr 1))) in

                      (* Gamma for under fix *)
                      let Γ' := (inl (Arrow IntType τ)::inr IntType::Γ) in

                      nr <- choose (1,2);;
                      loop_done <- backTrack nr (genTerm_terminating' ftv Γ' τ (sz / 2));;

                      nr <- choose (1,2);;
                      main_body <- backTrack nr (genTerm_terminating' ftv Γ' (Arrow τ τ) (sz / 2));;
                      let loop_main := App main_body (App (Var 0) count_dec) in

                      let f := Fix (Arrow IntType τ) IntType
                                   (If0 (Var 1)
                                        loop_done
                                        loop_main) in

                      returnGen (App f loop_start));
                  (* Type applications *)
                  (4, '(τ1, τ2) <- genT1T2 τ;;
                      me1 <- genTerm_terminating' ftv Γ τ1 (sz - 1);;
                      returnGen (TApp me1 τ2));
                  (* If0 *)
                  (1, c <- genTerm_terminating' ftv Γ IntType (sz / 3);;
                      e1 <- genTerm_terminating' ftv Γ τ (sz / 3);;
                      e2 <- genTerm_terminating' ftv Γ τ (sz / 3);;
                      returnGen (If0 c e1 e2))
                    (* TODO: unimplemented *)
                    (* Tuple projections *)
                    (* Annotated terms *)
                  ] ++
                    (match τ with
                     | Arrow τ1 τ2 =>
                       [(8, (arg <- genTerm_terminating' ftv (inl (Arrow τ1 τ2) :: inr τ1 :: Γ) τ2 (sz-1);;
                             returnGen (Fix (Arrow τ1 τ2) τ1 arg)))]
                     | TForall τ1 =>
                       [(4, (e <- genTerm_terminating' (ftv+1) (map (map_both (type_lift 0)) Γ) τ1 (sz-1);;
                             returnGen (TAbs e)))]
                     | Prod τs =>
                       [(1, (τs' <- map_monad (fun τ => genTerm_terminating' ftv Γ τ (sz / (length τs))) τs;;
                             returnGen (Tuple τs')))]
                     | IntType =>
                       [(* Operators *)
                         (1, op <- genPrimOp;;
                             e1 <- genTerm_terminating' ftv Γ IntType (sz / 2);;
                             e2 <- genTerm_terminating' ftv Γ IntType (sz / 2);;
                             returnGen (Op op e1 e2))]
                     | _ => []
                     end)
                 )
          )
      end.
  Admit Obligations.

  Definition genTerm_terminating (ftv : nat) (Γ : list (FType + FType)) (τ : FType) : G Term
    := sized (genTerm_terminating' ftv Γ τ).

  Instance GenFType : GenSized FType :=
    {| arbitrarySized n := genFType' 0 n |}.

  Definition genTypedTerm (n : nat) : G Term :=
    bindGen (genFType' 0 n) (fun τ => genTerm' 0 [] τ n).

  Instance GenTerm : GenSized Term :=
    {| arbitrarySized n := genTypedTerm n |}.
End Generators.

Section Shrinking.
  Fixpoint shrink_ftype (τ : FType) : list FType
    := match τ with
       | Arrow τ1 τ2 =>
         [IntType; τ1; τ2] ++
                           (τ1' <- shrink_ftype τ1;;
                            ret (Arrow τ1' τ2)) ++
                           (τ2' <- shrink_ftype τ2;;
                            ret (Arrow τ1 τ2'))
       | Prod τs => (IntType :: τs) ++ (τs' <- map_monad shrink_ftype τs;; ret (Prod τs'))
       | TForall τ' =>
         [IntType; τ'] ++ (τ'' <- shrink_ftype τ';; ret (TForall τ''))
       | TVar x => IntType :: (x' <- shrink x;; ret (TVar x'))
       | IntType => []
       end.

  (* Shrink, but without preserving well typedness *)
  Fixpoint shrink_term' {I} `{FInt I} (e : Term) : list Term
    := match e with
       | Var x =>
         Num zero :: (x' <- shrink x;; ret (Var x'))
       | Ann e τ =>
         Num zero :: e :: ((τ' <- shrink_ftype τ;; ret (Ann e τ')) ++ (e' <- shrink_term' e;; ret (Ann e' τ)))
       | Fix fτ aτ body =>
         Num zero :: body :: ((fτ' <- shrink_ftype fτ;; ret (Fix fτ' aτ body)) ++
                                                                            (aτ' <- shrink_ftype aτ;; ret (Fix fτ aτ' body)) ++
                                                                            (body' <- shrink_term' body;; ret (Fix fτ aτ body')))
       | App e1 e2 =>
         Num zero :: e1 :: e2 :: ((e1' <- shrink_term' e1;; ret (App e1' e2)) ++
                                                                          (e2' <- shrink_term' e2;; ret (App e1 e2')))
       | TAbs body => Num zero :: body :: (body' <- shrink_term' body;; ret (TAbs body'))
       | TApp e τ =>
         Num zero :: e :: ((τ' <- shrink_ftype τ;; ret (TApp e τ')) ++ (e' <- shrink_term' e;; ret (TApp e' τ)))
       | Tuple es =>
         Num zero :: es ++ (es' <- map_monad shrink_term' es;; ret (Tuple es'))
       | ProjN i e =>
         Num zero :: e :: (i' <- shrink i;; ret (ProjN i' e)) ++ (e' <- shrink_term' e;; ret (ProjN i e'))
       | Num x => []
       | If0 c e1 e2 =>
         Num zero :: c :: e1 :: e2 :: ((c' <- shrink_term' c;; ret (If0 c' e1 e2)) ++
                                                                              (e1' <- shrink_term' e1;; ret (If0 c e1' e2)) ++
                                                                              (e2' <- shrink_term' e2;; ret (If0 c e1 e2')))
       | Op op e1 e2 =>
         Num zero :: e1 :: e2 :: ((e1' <- shrink_term' e1;; ret (Op op e1' e2)) ++
                                                                            (e2' <- shrink_term' e2;; ret (Op op e1 e2')))
       end.

  Definition shrink_term_preserve_type {I} `{FInt I} (e : Term) : list Term
    := match step e with
       | inr e' =>
         if (term_size e') <? (term_size e)
         then [e']
         else []
       | inl _ => []
       end ++
           (let e' := multistep 500 e in
            if (term_size e') <? (term_size e)
            then [e']
            else []).

  Definition shrink_term {I} `{FInt I} (e : Term) : list Term
    := (e' <- shrink_term' e;; assert (well_typed e');; ret e') ++
                                                              (* Double shrinks in case first step isn't well_typed *)
                                                              (e' <- shrink_term' e;; e'' <- shrink_term' e';; assert (well_typed e'');; ret e'') ++
                                                              shrink_term_preserve_type e.

  (* Preserves typeof *)
  Definition shrink_term_filtered {I} `{FInt I} (e : Term) : list Term
    := filter (fun e' =>
                 match typeof e', typeof e with
                 | Some x, Some y => ftype_eq x y
                 | None, None => true
                 | _, _ => false
                 end) (shrink_term e).

  Instance shrFType : Shrink FType :=
    {| shrink := shrink_ftype |}.

  Instance shrTerm {I} `{FInt I} : Shrink Term :=
    {| shrink := shrink_term |}.
End Shrinking.


(* *** Testing *** *)
Definition factorial : @Term Int64.int FInt64
  := Fix (Arrow IntType IntType) IntType
         (If0 (Var 1)
              (Num (Int64.repr 1))
              (Op Mul (App (Var 0) (Op Sub (Var 1) (Num (Int64.repr 1)))) (Var 1))).


Unset Guard Checking.
Fixpoint run_eval (t : ITreeDefinition.itree Failure Term) : MlResult Term string
  := match observe t with
     | RetF x => MlOk _ string x
     | TauF t => run_eval t
     | VisF _ (Throw msg) k => MlError _ string msg
     end.
Set Guard Checking.

(* ** FType Tests ** *)
Definition ftype_eq_refl (τ : FType) : bool
  := ftype_eq τ τ.

QuickCheck (forAll (genFType 0) (well_formed_type 0)).
QuickCheck (forAll (genFType 10) ftype_eq_refl).

(* Generated terms have types *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm 0 [] τ)
                                              (fun e => match typeof e with
                                                     | Some τ' =>
                                                       ftype_eq τ τ'
                                                     | _ => false
                                                     end))).

QuickCheck (forAll (genFType 0) (fun τ => forAllShrink (genTerm_terminating 0 [] τ) shrink_term_filtered
                                              (fun e => match typeof e with
                                                     | Some τ' =>
                                                       whenFail
                                                         ("Bad type: " ++ show τ')
                                                         (ftype_eq τ τ')
                                                     | _ =>
                                                       whenFail
                                                         "No type"
                                                         false
                                                     end))).

(* Test for preservation *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm 0 [] τ)
                                              (fun e => match step e with
                                                     | inr e' =>
                                                       match typeof e', typeof e with
                                                       | Some τ1, Some τ2 => ftype_eq τ1 τ2
                                                       | _, _ => true
                                                       end
                                                     | _ => true
                                                     end))).

(* Test that we evaluate without failing *)
QuickCheck (forAll (genFType 0) (fun τ => forAllShrink (genTerm_terminating 0 [] τ) shrink_term_filtered
                                              (fun e => match run_eval (eval e) with
                                                     | MlOk _ =>
                                                       checker true
                                                     | MlError x =>
                                                       whenFail x
                                                       false
                                                     end))).

(* Eval preserves types *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm_terminating 0 [] τ)
                                              (fun e => match run_eval (eval e) with
                                                     | MlOk e' =>
                                                       match typeof e', typeof e with
                                                       | Some τ1, Some τ2 =>
                                                         whenFail
                                                           (show ((e', τ1), (e, τ2)))
                                                           (ftype_eq τ1 τ2)
                                                       | _, _ => checker true
                                                       end
                                                     | MlError x =>
                                                       whenFail x
                                                       false
                                                     end))).

(* Eval gives a value *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm_terminating 0 [] τ)
                                              (fun e => match run_eval (eval e) with
                                                     | MlOk e' =>
                                                       whenFail
                                                         ("Not a value: " ++ show e')
                                                         (is_value e')
                                                     | MlError x =>
                                                       whenFail x
                                                       false
                                                     end))). 


(* Eval matches multistep *)
(* Fails because of tuples *)
(* QuickCheck (forAll (genFType 0) (fun τ => forAllShrink (genTerm_terminating 0 [] τ) shrink_term_preserve_type *)
(*                                               (fun e => match run_eval (eval e) with *)
(*                                                      | MlOk x => *)
(*                                                        match multistep' 10000 e with *)
(*                                                        | Some y => whenFail (show (x,y)) (term_eq x y) *)
(*                                                        | None => checker true (* Should probably make this a discard *) *)
(*                                                        end *)
(*                                                      | MlError x => *)
(*                                                        whenFail x *)
(*                                                        false *)
(*                                                      end))). *)
