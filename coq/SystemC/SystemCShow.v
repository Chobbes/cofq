From Cofq.SystemC Require Import SystemCDefinitions.
From Cofq.BaseExpressions Require Import Integers.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import String List.
Open Scope string_scope.

Require Import QuickChick.

Fixpoint showCType' (t : CType) :=
  match t with
  | CProd ts => "CProd " ++ show (map showCType' ts)
  | CTForall n ts => "CTForall " ++ show n ++ " " ++ show (map showCType' ts)
  | CTVar x => "CTVar " ++ show x
  | CIntType => "CIntType"
  | CTExists t => "CTExists " ++ showCType' t
  end.

Instance showCType : Show CType := 
  {| show := showCType'
  |}.

Fixpoint showCValue' {I} `{FInt I} `{Show I} (v : CValue) :=
  match v with
  | CAnnotated rv t => "CAnnotated (" ++ showCRawValue' rv ++ ") (" ++ show t ++ ")"
  end
with showCRawValue' {I} `{FInt I} `{Show I} (rv : CRawValue) :=
       match rv with
       | CNum x => "CNum (" ++ show x ++ ")"
       | CVar x => "CVar (" ++ show x ++ ")"
       | CTuple x => "CTuple " ++ show (map showCValue' x)
       | CPack t1 rv t2 => "CPack (" ++ show t1 ++ ") (" ++ showCRawValue' rv ++ ") (" ++ show t2 ++ ")"
       | CTApp rv τ => "CTApp (" ++ showCRawValue' rv ++ ") (" ++ show τ ++ ")"
       end.

Instance showCValue {I} `{FInt I} `{Show I} : Show CValue :=
  {| show := showCValue'
  |}.

Instance showCRawValue {I} `{FInt I} `{Show I} : Show CRawValue :=
  {| show := showCRawValue'
  |}.

Definition showCDeclaration' {I} `{FInt I} `{Show I} (d : CDeclaration) :=
  match d with
  | CVal x => "CVal (" ++ show x ++ ")"
  | CProjN i v => "CProjN (" ++ show i ++ ") (" ++ show v ++ ")"
  | COp op v1 v2 => "COp " ++ show op ++ " (" ++ show v1 ++ ") (" ++ show v2 ++ ")"
  | CUnpack x => "CUnpack (" ++ show x ++ ")"
  end.

Instance showCDeclaration {I} `{FInt I} `{Show I} : Show CDeclaration :=
  {| show := showCDeclaration'
  |}.

Fixpoint showCTerm' {I} `{FInt I} `{Show I} (term : CTerm) :=
  match term with
  | CLet dec v =>
    "CLet (" ++ show dec ++ ") (" ++ showCTerm' v ++ ")"
  | CApp f vs =>
    "CApp (" ++ show f  ++ ") " ++ show vs
  | CIf0 c e1 e2 =>
    "CIf0 (" ++ show c ++ ") (" ++ showCTerm' e1 ++ ") (" ++ showCTerm' e2 ++ ")"
  | CHalt x τ =>
    "CHalt (" ++ show x ++ ") (" ++ show τ ++ ")"
  end.

Instance showCTerm {I} `{FInt I} `{Show I} : Show CTerm :=
  {| show := showCTerm'
  |}.
