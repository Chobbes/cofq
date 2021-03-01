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
  | TVar x => show x
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
  | Var x => show x
  | Ann e t => parens prec PrecOuter (showTerm_helper PrecOuter e ++ " : " ++ show t)
  | Fix t body => parens prec PrecOuter ("λ " ++ show t ++ ". " ++ showTerm_helper PrecOuter body)
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

QuickCheck (forAll (genFType 10) ftype_eq_refl).

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
               [τ' <- replace_sub_type (n+1) τ arg_τ;;
                returnGen (TForall τ')
               ]
             | _ => []
             end).

(* Generate t1 t2 such that t1{0:=t2} = t *)
Definition genT1T2 (τ : FType) : G (FType * FType)
  := let τ' := type_lift 0 τ
     in τ2 <- fetch_sub_type τ';;
        τ1 <- replace_sub_type 0 τ' τ2;;
        returnGen (TForall τ1, τ2).

Definition genPrimOp : G PrimOp
  := oneOf_ failGen (map returnGen [Mul; Add; Sub]).

(* Probably want a variant of this that won't make recursive calls *)
Program Fixpoint genTerm' (ftv : nat) (Γ : list FType) (τ : FType) (sz : N) {measure (N.to_nat sz)} : G Term
  :=
    match sz with
    | N0 =>
      oneOf_ failGen
             ( (guard (ftype_eq IntType τ);; ret (fmap Num genInt64)) ++
               (* Generate variables from the context with the same type *)
               ('(i,τ') <- addIndices Γ;; guard (ftype_eq τ' τ);; ret (returnGen (Var i))) ++
               (* Generate fixpoints... Need a way of ruling out recursive applications *)
               (match τ with
                | Arrow τ1 τ2 =>
                  [arg <- genTerm' ftv (τ1 :: Γ) τ2 0;;
                   returnGen (Fix τ1 arg)
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
    | Npos x =>
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
                         returnGen (If0 c e1 e2));
                     (* Operators *)
                     (1, op <- genPrimOp;;
                         e1 <- genTerm' ftv Γ τ (sz / 2);;
                         e2 <- genTerm' ftv Γ τ (sz / 2);;
                         returnGen (Op op e1 e2))
                     (* TODO: unimplemented *)
                     (* Tuple projections *)
                     (* Annotated terms *)
                    ] ++
                    (match τ with
                     | Arrow τ1 τ2 =>
                       [(8, (arg <- genTerm' ftv (τ1 :: Γ) τ2 (sz-1);;
                             returnGen (Fix τ1 arg)))]
                     | TForall τ1 =>
                       [(4, (e <- genTerm' (ftv+1) (map (type_lift 0) Γ) τ1 (sz-1);;
                                returnGen (TAbs e)))]
                     | Prod τs =>
                       [(1, (τs' <- map_monad (fun τ => genTerm' ftv Γ τ (sz / (N.of_nat (length τs)))) τs;;
                             returnGen (Tuple τs')))]
                     | _ => []
                     end)
                   )
            )
    end.
Next Obligation.
Admitted.

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

Definition factorial : @Term Int64.int FInt64
  := Fix IntType
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
