From Cofq.SystemK Require Import SystemKDefinitions.
From Cofq.BaseExpressions Require Import Integers.
From Cofq.Show Require Import ShowUtils.

From Coq Require Import String List.
Open Scope string_scope.

Require Import QuickChick.

Fixpoint showKType' (t : KType) :=
  match t with
  | KProd ts => "KProd " ++ show (map showKType' ts)
  | KTForall n ts => "KTForall " ++ show n ++ " " ++ show (map showKType' ts)
  | KTVar x => "KTVar " ++ show x
  | KIntType => "KIntType"
  end.

Instance showKType : Show KType := 
  {| show := showKType'
  |}.
(*
Fixpoint showKValue' {I} `{FInt I} `{Show I} (v : KValue) :=
  match v with
  | KAnnotated t rv => "KAnnotated (" ++ showKRawValue' rv ++ ") (" ++ show t ++ ")"
  end
with showKRawValue' {I} `{FInt I} `{Show I} (rv : KRawValue) :=
       match rv with
       | KNum x => "CNum (" ++ show x ++ ")"
       | KVar x => "CVar (" ++ show x ++ ")"
       | KTuple x => "CTuple " ++ show (map showKValue' x)
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
*)