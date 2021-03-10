From Coq Require Import
     String.

From QuickChick Require Import Show.
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
