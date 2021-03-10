From Coq Require Import List Lia.

Global Open Scope list_scope.

(* Check that a predicate holds elementwise across two lists, while
   also making sure that the lists have equal length.
*)
Fixpoint zip_pred {X Y} (pred : X -> Y -> bool) (xs : list X) (ys : list Y) : bool
  := match xs, ys with
     | nil, nil => true
     | x::xs, y::ys => pred x y && zip_pred pred xs ys
     | _, _ => false
     end.

Lemma list_sum_map :
  forall {X} (f : X -> nat) x xs,
    In x xs ->
    list_sum (map f xs) >= f x.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs H).
    unfold list_sum in IHxs.
    lia.
Qed.

Lemma map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
Proof.
  induction l.
  - exact nil.
  - refine (f a _ :: IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Fixpoint zipwith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z
  := match xs, ys with
     | (x :: xs), (y :: ys) => f x y :: (zipwith f xs ys)
     | _, _ => nil
     end.
