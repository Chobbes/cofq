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

Require Import SystemF.

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

Instance showTerm {I} `{FInt I} `{Show I} : Show Term :=
  {| show := showTerm_helper PrecOuter
  |}.

Require Import Lia.

Check map TVar (map N.of_nat (seq 0 1)).

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
