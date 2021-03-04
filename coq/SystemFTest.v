From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

From Coq Require Import
     ZArith
     String
     List.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From Vellvm Require Import
     Numeric.Integers
     Utils.Util.

Require Import SystemF.
Require Import Lia.


Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Variant Precedence :=
| PrecOuter
| PrecMult
| PrecAdd
| PrecSub
| PrecApp
| PrecInner
.

Definition prec_value (p : Precedence) : N :=
  match p with
  | PrecOuter => 0
  | PrecAdd => 1
  | PrecSub => 1
  | PrecMult => 2
  | PrecApp => 3
  | PrecInner => 4
  end.

Definition parens (outer inner : Precedence) (s : string) :=
  if N.leb (prec_value outer) (prec_value inner)
  then s
  else "(" ++ s ++ ")".

Definition intersperse (sep : string) (l : list string) : string
  := fold_left (fun acc s => if eqb "" acc then s else s ++ sep ++ acc) l "".

Fixpoint showFType_helper (prec : Precedence) (t : FType) :=
  match t with
  | Arrow a b => parens prec PrecApp (showFType_helper PrecInner a ++ "->" ++ showFType_helper PrecApp b)
  | Prod ts => "<" ++ intersperse ", " (map (showFType_helper PrecOuter) ts) ++ ">"
  | TForall t => parens prec PrecOuter ("forall " ++ showFType_helper PrecOuter t)
  | TVar x => "t" ++ show x
  | IntType => "Int"
  end.

Instance showFType : Show FType := 
  {| show := showFType_helper PrecOuter
  |}.

Instance showPrimOp : Show PrimOp :=
  {| show :=
       fun (op : PrimOp) =>
         match op with
         | Mul => "*"
         | Add => "+"
         | Sub => "-"
         end
  |}.

Definition op_prec (op : PrimOp) : Precedence
  := match op with
     | Mul => PrecMult
     | Add => PrecAdd
     | Sub => PrecSub
     end.           

Fixpoint showTerm_helper {I} `{FInt I} `{Show I} (prec : Precedence) (e : Term) :=
  match e with
  | Var x => "v" ++ show x
  | Ann e t => parens prec PrecOuter (showTerm_helper PrecOuter e ++ " : " ++ show t)
  | Fix ft t body => parens prec PrecOuter ("λ " ++ show ft ++ " " ++ show t ++ ". " ++ showTerm_helper PrecOuter body)
  | TAbs e => parens prec PrecOuter ("Λ. " ++ showTerm_helper PrecOuter e)
  | App e1 e2 => parens prec PrecInner (showTerm_helper PrecInner e1 ++ " " ++ showTerm_helper PrecApp e2)
  | TApp e t => parens prec PrecInner (showTerm_helper PrecInner e ++ " [" ++ show t ++ "]")
  | Tuple es => "<" ++ intersperse ", " (map (showTerm_helper PrecOuter) es) ++ ">"
  | ProjN i e => parens prec PrecInner ("π" ++ show i ++ " " ++ showTerm_helper PrecApp e)
  | Num n => show n
  | If0 c e1 e2 => parens prec PrecApp ("if0 " ++ showTerm_helper PrecOuter c ++ " then " ++ showTerm_helper PrecOuter e1 ++ " else " ++ showTerm_helper PrecOuter e2)
  | Op op e1 e2 =>
    let oprec := op_prec op in
    parens prec oprec (showTerm_helper oprec e1 ++ " " ++ show op ++ " " ++ showTerm_helper oprec e2) 
  end.

Instance showInt64 : Show Int64.int :=
  {| show := fun i => show (Int64.intval i)
  |}.

Instance showTerm {I} `{FInt I} `{Show I} : Show Term :=
  {| show := showTerm_helper PrecOuter
  |}.


Definition elems_fail {A : Type} (l : list A) :=
  let n := length l in
  bindGen (choose (0, n - 1))
          (fun n' =>
             match (List.nth_error l n') with
             | Some x => returnGen x
             | None => failGen
             end).

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

(* ** FType Tests ** *)
Definition ftype_eq_refl (τ : FType) : bool
  := ftype_eq τ τ.

Definition genInt64 : G Int64.int
  := z <- arbitrary;;
     ret (Int64.repr z).

Definition genIfType {A} (τ1 τ2 : FType) (g : G A) : list (G A)
  := if ftype_eq τ1 τ2 then [g] else [].

Definition guard (b : bool) : list unit
  := if b
     then [tt]
     else [].


Compute guard (ftype_eq IntType (TVar 2));; ret 2.

Fixpoint addIndices' {A} (i : N) (l : list A) : list (N * A)
  := match l with
     | nil => nil
     | (x::xs) => (i,x) :: addIndices' (N.succ i) xs
     end.

Definition addIndices {A} := @addIndices' A 0.

(* TODO: Add this to QC and make it actually do something *)
Definition takeG {A} (n : nat) (g : G A) : G A := g.

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

(* Randomly fetch a subterm of a type *)
Fixpoint fetch_sub_type (τ : FType) : G FType
  :=
    oneOf_ failGen
           ((guard (is_closed τ);; [returnGen τ]) ++
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
             (guard (ftype_eq τ arg_τ);; [returnGen (TVar n)]) ++
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
               guard (ftype_eq τ arg_τ);;
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

Definition genPrimOp : G PrimOp
  := oneOf_ failGen (map returnGen [Mul; Add; Sub]).

(* Probably want a variant of this that won't make recursive calls *)
Program Fixpoint genTerm' (ftv : nat) (Γ : list FType) (τ : FType) (sz : nat) {measure sz} : G Term
  :=
    match sz with
    | 0 =>
      oneOf_ failGen
             ( (guard (ftype_eq IntType τ);; ret (fmap Num genInt64)) ++
               (* Generate variables from the context with the same type *)
               ('(i,τ') <- addIndices Γ;; guard (ftype_eq τ' τ);; ret (returnGen (Var i))) ++
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

Definition map_both {A B} (f : A -> B) (e : A + A) :=
  match e with
  | inl a => inl (f a)
  | inr a => inr (f a)
  end.

(* inl means it's a fixpoint variable *)
Program Fixpoint genTerm_terminating' (ftv : nat) (Γ : list (FType + FType)) (τ : FType) (sz : nat) {measure sz} : G Term
  :=
    match sz with
    | 0 =>
      oneOf_ failGen
             ( (guard (ftype_eq IntType τ);; ret (fmap Num genInt64)) ++
               (* Generate variables from the context with the same type *)
               ('(i,mτ) <- addIndices Γ;; 
                match mτ with
                | inr τ' =>
                  guard (ftype_eq τ' τ);; ret (returnGen (Var i))
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


(* Want to be able to generate basic loops... But don't want general recursion...

   Make it so I can rule out the variable for the recursive call.

   Make it so that I can call recursively if the argument, n, has IntType,
   and if I force the recursive call to be applied to (n-1), *AND* the body
   of the fix starts with if0.
 *)
(* Fix τ
    (if0 (Var 1) (* this is the argument to fix *)
    (call with Var 0 (f), and then (Var 1 - Num 1)) (* Make a decreasing call *)
    (something-that-can't-access Var 0)
     )
*)

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

Definition well_typed {I} `{FInt I} (e : Term) : bool
  := ssrbool.isSome (typeof e).

Definition shrink_term_preserve_type {I} `{FInt I} (e : Term) : list Term
  := match step e with
     | inr e' =>
       if (term_size e') <? (term_size e)
       then [e']
       else []
     | inl _ => []
     end.

Definition shrink_term {I} `{FInt I} (e : Term) : list Term
  := (e' <- shrink_term' e;; guard (well_typed e');; ret e') ++
     (* Double shrinks in case first step isn't well_typed *)
     (e' <- shrink_term' e;; e'' <- shrink_term' e';; guard (well_typed e'');; ret e'') ++
     shrink_term_preserve_type e.

Instance shrFType : Shrink FType :=
  {| shrink := shrink_ftype |}.

Instance shrTerm {I} `{FInt I} : Shrink Term :=
  {| shrink := shrink_term |}.

Instance GenFType : GenSized FType :=
  {| arbitrarySized n := genFType' 0 n |}.

Definition genTypedTerm (n : nat) : G Term :=
  bindGen (genFType' 0 n) (fun τ => genTerm' 0 [] τ n).

Instance GenTerm : GenSized Term :=
  {| arbitrarySized n := genTypedTerm n |}.


(* *** Testing *** *)
Definition factorial : @Term Int64.int FInt64
  := Fix (Arrow IntType IntType) IntType
         (If0 (Var 1)
              (Num (Int64.repr 1))
              (Op Mul (App (Var 0) (Op Sub (Var 1) (Num (Int64.repr 1)))) (Var 1))).

Definition step' (v : unit + Term) : (unit + Term)
  := match v with
     | inl tt => inl tt
     | inr t => step t
     end.

Fixpoint multistep (n : nat) (v : Term) : Term
  := match n with
     | O => v
     | S n =>
       match step v with
       | inl tt => v
       | inr t => multistep n t
       end
     end.

Compute (multistep 100 (App factorial (Num (Int64.repr 3)))).

QuickCheck (forAll (genFType 0) (well_formed_type 0)).
QuickCheck (forAll (genFType 10) ftype_eq_refl).

(* Generated terms have types *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm 0 [] τ)
                                              (fun e => match typeof e with
                                                     | Some τ' =>
                                                       ftype_eq τ τ'
                                                     | _ => false
                                                     end))).

QuickCheck (forAll (genFType 0) (fun τ => forAllShrink (genTerm_terminating 0 [] τ) shrink_term_preserve_type
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


From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.


Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Unset Guard Checking.
Fixpoint run_eval (t : ITreeDefinition.itree Failure Term) : MlResult Term string
  := match observe t with
     | RetF x => MlOk _ string x
     | TauF t => run_eval t
     | VisF _ (Throw msg) k => MlError _ string msg
     end.
Set Guard Checking.

Instance showMLResult {A E} `{Show A} `{Show E} : Show (MlResult A E)
  := {| show :=
          fun mlr =>
            match mlr with
            | MlOk x => "MlOk " ++ show x
            | MlError x => "MlError " ++ show x
            end
    |}.


(* Test that we evaluate without failing *)
QuickCheck (forAll (genFType 0) (fun τ => forAll (genTerm_terminating 0 [] τ)
                                              (fun e => match run_eval (eval e) with
                                                     | MlOk _ =>
                                                       checker true
                                                     | MlError x =>
                                                       whenFail x
                                                       false
                                                     end))).

(*
Extract Constant defNumTests    => "1".
QuickChick (checker
              (let e := (run_eval (eval (App (Num zero) (Op Mul (Num (Int64.repr 4)) (Num (Int64.repr 3)))))) in
              collect e
              (match e with
               | MlOk (Num x) => eq x (Int64.repr 12)
               | _ => false
               end))
           ).

QuickChick (checker (match (run_eval (eval (App (Fix (Arrow IntType IntType) IntType (Op Mul (Var 1) (Num (Int64.repr 4)))) (Num (Int64.repr 3))))) with
                     | MlOk (Num x) => eq x (Int64.repr 12)
                     | _ => false
                       end)
           ).

QuickChick (checker
              ( let e := run_eval (eval (App factorial (Num (Int64.repr 5)))) in
                collect e true)).
*)
