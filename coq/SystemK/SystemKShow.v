From Cofq.SystemF Require Import SystemFDefinitions.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import String.
Open Scope string_scope.

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

Instance showTerm {I} `{FInt I} `{Show I} : Show Term :=
  {| show := showTerm_helper PrecOuter
  |}.
