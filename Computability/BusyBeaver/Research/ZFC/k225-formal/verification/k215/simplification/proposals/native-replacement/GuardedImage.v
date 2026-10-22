(* Mathematical proof draft. Not compiled in this review.
   This is a pure native-equality lemma, not a replacement for raw bisimilarity. *)
Section GuardedImage.
  Context {V : Type} (mem R : V -> V -> Prop) (a b : V).
  Hypothesis support : forall y, mem y b -> exists x, mem x a /\ R x y.
  Hypothesis cover : forall x, mem x a -> (exists y, R x y) ->
    exists y, mem y b /\ R x y.
  Hypothesis functional : forall x y z, mem x a -> R x y -> R x z -> y = z.

  Lemma guarded_image : forall y, mem y b <-> exists x, mem x a /\ R x y.
  Proof.
    intro y; split.
    - apply support.
    - intros [x [hxa hxy]].
      destruct (cover x hxa (ex_intro _ y hxy)) as [z [hzb hxz]].
      assert (hyz : y = z) by (eapply functional; eauto).
      rewrite hyz; exact hzb.
  Qed.
End GuardedImage.
