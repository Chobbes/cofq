From Coq Require Import
     ZArith
     String
     List.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* I don't know why, but I need this to make Extract Inductive work below... *)
From ITree Require Import
     ITree.

Global Open Scope string_scope.

Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e
.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Instance showMLResult {A E} `{Show A} `{Show E} : Show (MlResult A E)
  := {| show :=
          fun mlr =>
            match mlr with
            | @MlOk _ _ x => "MlOk " ++ show x
            | @MlError _ _ x => "MlError " ++ show x
            end
    |}.

Fixpoint addIndices' {A} (i : N) (l : list A) : list (N * A)
  := match l with
     | nil => nil
     | (x::xs) => (i,x) :: addIndices' (N.succ i) xs
     end.

Definition addIndices {A} := @addIndices' A 0.

Definition map_both {A B} (f : A -> B) (e : A + A) : B + B :=
  match e with
  | inl a => inl (f a)
  | inr a => inr (f a)
  end.

Definition elems_fail {A : Type} (l : list A) :=
  let n := List.length l in
  bindGen (choose (0, n - 1))
          (fun n' =>
             match (List.nth_error l n') with
             | Some x => returnGen x
             | None => failGen
             end).
