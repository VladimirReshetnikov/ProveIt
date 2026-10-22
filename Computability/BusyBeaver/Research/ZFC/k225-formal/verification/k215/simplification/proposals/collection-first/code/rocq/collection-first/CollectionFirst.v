(** Constructive semantic core of the collection-first quotient proposal.
    The two definitions match ProfileCollection.lean at the pinned review
    commit. Only the displayed relation instance is assumed. *)
Set Implicit Arguments.

Section CollectionFirst.
Context {V : Type}.
Variable mem : V -> V -> Prop.

Definition ImageCollection (r : V -> V -> Prop) (a b : V) : Prop :=
  (forall y, mem y b -> exists x, r x y) /\
  (forall x, mem x a -> (exists y, r x y) ->
    exists y, mem y b /\ r x y).

Definition CollectionInstance (r : V -> V -> Prop) : Prop :=
  forall a, exists b, ImageCollection r a b.

Theorem exact_image_of_collection (r : V -> V -> Prop) (a : V)
  (functional : forall x y z, mem x a -> r x y -> r x z -> y = z)
  (collect : CollectionInstance (fun x y => mem x a /\ r x y)) :
  exists b, forall y, mem y b <-> exists x, mem x a /\ r x y.
Proof.
  destruct (collect a) as [b [support cover]].
  exists b. intro y. split.
  - apply support.
  - intros [x [hxa hxy]].
    assert (some : exists z, mem x a /\ r x z).
    { exists y. split; assumption. }
    destruct (cover x hxa some) as [z [hzb [_ hxz]]].
    rewrite (functional x z y hxa hxz hxy) in hzb.
    exact hzb.
Qed.

Theorem separation_of_collection (p : V -> Prop) (a : V)
  (collect : CollectionInstance
    (fun x y => mem x a /\ (x = y /\ p x))) :
  exists b, forall y, mem y b <-> mem y a /\ p y.
Proof.
  assert (functional : forall x y z, mem x a ->
    (x = y /\ p x) -> (x = z /\ p x) -> y = z).
  { intros x y z _ [hxy _] [hxz _]. now rewrite <- hxy, <- hxz. }
  destruct (exact_image_of_collection
    (fun x y => x = y /\ p x) (a := a) functional collect) as [b hb].
  exists b. intro y. split.
  - intro hy. destruct (proj1 (hb y) hy) as [x [hxa [hxy hp]]].
    now subst y.
  - intros [hya hp]. apply (proj2 (hb y)). exists y. split; [assumption|].
    split; [reflexivity|assumption].
Qed.
End CollectionFirst.

Print Assumptions exact_image_of_collection.
Print Assumptions separation_of_collection.
