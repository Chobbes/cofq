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

(* Probably want a variant of this that won't make recursive calls *)
Program Fixpoint genTerm' (ftv : nat) (Γ : list FType) (τ : FType) (sz : N) : G Term
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
                  ret (arg <- genTerm' ftv (τ1 :: Γ) τ2 0;;
                       returnGen (Fix τ1 arg))
                | _ => []
                end) ++
               (match τ with
                | TForall τ1 =>
                  ret (
                    )
                | _ => []
                end)
               (* Tuples *)
               
             )
    | Npos x => _
    end.
Next Obligation.
Admitted.


[ return $ Var i | (i,t') <- zip [0..] c, t == t' ] ++
[ Lam t1 <$> arb ftv (t1:c) t2 0 | (t1 :-> t2) <- [t] ] ++
[ TLam <$> arb (ftv+1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t] ]   -- MUTANT?

  match sz with
     | O =>
     | S x => _
     end.
Inductive Term {I} `{FInt I} : Type :=
| Var          : VarInd -> Term (* *)
(* Annotated terms *)
| Ann          : Term -> FType -> Term
(* Terms *)
| Fix          : FType -> Term -> Term (* *)
| App          : Term -> Term -> Term
(* Type stuff *)
| TAbs         : Term -> Term
| TApp         : Term -> FType -> Term
(* Prod *)
| Tuple        : list Term -> Term 
| ProjN        : N -> Term -> Term
(* Int *)
| Num          : I -> Term
(* Expressions *)
| If0          : Term -> Term -> Term -> Term
| Op           : PrimOp -> Term -> Term -> Term
.


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

(*       
genExpr :: _ => Gen Expr
genExpr =
--  traceShow (?config, ?mutant) $
  (gcTake ?config) $ sized $ (\n -> do t <- genType 0; arb 0 [] t n)
    where arb :: Int -> [Type] -> Type -> Int -> Gen Expr
          arb ftv c t 0 = (gcBaseChoice ?config) $
                          [ return Con | t == Base ] ++
--                          [ return BTrue | t == TBool ] ++
--                          [ return BFalse | t == TBool ] ++                          [ return $ Var i | (i,t') <- zip [0..] c, t == t' ] ++
                          [ Lam t1 <$> arb ftv (t1:c) t2 0 | (t1 :-> t2) <- [t] ] ++
                          [ TLam <$> arb (ftv+1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t] ]   -- MUTANT?
          arb ftv c t n = (takeG $ gcRecChoiceTake ?config) . (gcRecChoice ?config) $
                          [ (6, arb ftv c t 0) ] ++
                          [ (8, Lam t1 <$> (arb ftv (t1:c) t2 (n-1))) | (t1 :-> t2) <- [t] ] ++
                          [ (4, TLam <$> (arb (ftv+1) (map (liftType 0) c) t1 (n-1))) | (ForAll t1) <- [t] ] ++
                          [ (8, do t2 <- retry (gcRetryType ?config) $ do
                                         arbT <- resize 10 $ genType ftv   -- for now; should be bigger?
                                         -- TODO: Michal?
                                         elements (nub $ michal c t ++ [arbT])
                                   nr <- choose (1,2)
                                   me1 <- retry nr $ arb ftv c (t2 :-> t) (n `div` 2)
                                   me2 <- arb ftv c t2 (n `div` 2)
                                   return $ me1 :@: me2) ] ++
                          [ (4, do (t1, t2) <- retry (gcRetryTApp ?config) $ genT1T2 t
                                   me1 <- arb ftv c t1 (n - 1)
                                   return $ TApp me1 t2) ] {- ++
                         [ (1, do e1 <- arb ftv c TBool (n `div` 3)
                                  e2 <- arb ftv c t (n `div` 3)
                                  e3 <- arb ftv c t (n `div` 3)
                                  return $ Cond e1 e2 e3) ] -}


michal c t = [t' | varType <- c,
                   t' <- aux varType]
  where aux (t1 :-> t2) | t==t2 = [t1]
                        | t/=t2 = aux t2
        aux _                   = []


-- Check if a type has any type variables.
-- TODO: replace with "isClosed"
hasTVars :: Type -> Bool
hasTVars (TVar _)    = True
hasTVars (t1 :-> t2) = hasTVars t1 || hasTVars t2
hasTVars (ForAll t)  = hasTVars t
hasTVars TBool       = False
hasTVars Base        = False


isClosed :: Type -> Bool
isClosed = isClosed' 0
  where
    isClosed' :: Int -> Type -> Bool
    isClosed' tc (TVar x)    = x < tc
    isClosed' tc (t1 :-> t2) = isClosed' tc t1 && isClosed' tc t2
    isClosed' tc (ForAll t)  = isClosed' (tc+1) t
    isClosed' _ TBool        = True
    isClosed' _ Base         = True

-- Randomly fetch a subterm of a type
fetchSubType :: Type -> Gen Type
fetchSubType t =
  oneof $
  [ return t | isClosed t ] ++
  [ fetchSubType t1 | (t1 :-> t2) <- [t] ] ++
  [ fetchSubType t2 | (t1 :-> t2) <- [t] ] ++
  [ fetchSubType t' | (ForAll t') <- [t] ]

replaceSubType :: Int -> Type -> Type -> Gen Type
-- "Replace (some occurrences of) closed type s in type t by (TVar n)"
replaceSubType n s t =
  oneof $
  [ return t ] ++
  [ return $ TVar n | s == t ] ++
  [ do t1' <- replaceSubType n s t1; t2' <- replaceSubType n s t2; return $ t1' :-> t2' | (t1 :-> t2) <- [t] ] ++
  [ do t'' <- replaceSubType (n+1) s t'; return $ ForAll t'' | (ForAll t') <- [t], t' == s ]

-- Generate t1 t2 such that t1{0:=t2} = t
genT1T2 :: Type -> Gen (Type, Type)
genT1T2 t = do
  let t' = let ?mutant = NoMutant in liftType 0 t
  t2 <- fetchSubType t'
  t1 <- replaceSubType 0 t2 t'
  return (ForAll t1, t2)
*) 
