From Coq Require Import
     String.

From QuickChick Require Import QuickChick.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

Require Import SystemF.

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
