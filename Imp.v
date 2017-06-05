(** Exercise: 3 stars (optimize_0plus_b)
Since the optimize_0plus transformation doesn't change the value of aexps, 
we should be able to apply it to all the aexps that appear in a bexp without changing the bexp's value. 
Write a function which performs that transformation on bexps, and prove it is sound. 
Use the tacticals we've just seen to make the proof as elegant as possible. **)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue =>
      BTrue
  | BFalse =>
      BFalse
  | BEq e1 e2 =>
      BEq (optimize_0plus e1) (optimize_0plus e2)
  | BLe e1 e2 =>
      BLe (optimize_0plus e1) (optimize_0plus e2)
  | BNot b =>
      BNot b
  | BAnd b1 b2 =>
      BAnd b1 b2
  end.

Theorem optimize_0plus_b_sound : ∀b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. induction b; simpl;
  try (rewrite optimize_0plus_sound);
  try (rewrite optimize_0plus_sound);
  reflexivity.
Qed.
