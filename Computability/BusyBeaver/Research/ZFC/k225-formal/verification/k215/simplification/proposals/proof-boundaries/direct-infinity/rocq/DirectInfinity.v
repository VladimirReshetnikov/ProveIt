(** Direct Infinity from the precise seed-property shape used by KSeed222.
    This standalone mathematical core has no project imports.
    The actual FormSeed schema and K215 endpoint are not instantiated here.
    [SuccRel] makes representative equality explicit, so tagged subtypes do
    not require a proof-irrelevance axiom in Rocq. *)
Set Universe Polymorphism.

Definition Seed {V : Type} (mem R : V -> V -> Prop) (A : V) : Prop :=
  exists C, (forall y, R A y -> exists z, R A z /\ mem z C) /\
    forall y, mem y C -> exists x, R x y /\
      forall x', (forall w, mem w x' -> mem w y) ->
        forall y', R x' y' -> exists z, R x' z /\ mem z C.

Definition SuccRel {V : Type} (mem E : V -> V -> Prop) (x y : V) : Prop :=
  forall z, mem z y <-> mem z x \/ E z x.

Definition Succ {V : Type} (mem : V -> V -> Prop) (x y : V) : Prop :=
  SuccRel mem eq x y.

Definition InductiveRel {V : Type} (mem E : V -> V -> Prop) (e I : V) : Prop :=
  mem e I /\ forall x, mem x I -> exists y, mem y I /\ SuccRel mem E x y.

Definition InductiveSet {V : Type} (mem : V -> V -> Prop) (e I : V) : Prop :=
  InductiveRel mem eq e I.

Theorem seed_serial_container {V : Type} (mem R : V -> V -> Prop)
    (P : V -> Prop) (a : V) (ha : P a)
    (range : forall x y, R x y -> P y)
    (serial : forall x, P x -> exists y, R x y)
    (seed : Seed mem R a) :
  exists C, (exists y, R a y /\ mem y C) /\
    (forall y, mem y C -> P y) /\
    forall y, mem y C -> exists z, R y z /\ mem z C.
Proof.
  destruct seed as [C [Hroot Hclosed]].
  assert (tags : forall y, mem y C -> P y).
  { intros y Hy. destruct (Hclosed y Hy) as [x [Hxy _]]. exact (range x y Hxy). }
  exists C. split.
  - destruct (serial a ha) as [y Hy]. exact (Hroot y Hy).
  - split; [exact tags|]. intros y Hy.
    destruct (Hclosed y Hy) as [x [Hxy Hnext]].
    destruct (serial y (tags y Hy)) as [z Hyz].
    exact (Hnext y (fun w Hw => Hw) z Hyz).
Qed.

Theorem succ_tag {V : Type} {mem : V -> V -> Prop} {t x y : V}
    (hx : mem t x) (h : Succ mem x y) : mem t y.
Proof. exact (proj2 (h t) (or_introl hx)). Qed.

Theorem seed_tagged_container {V : Type} (mem : V -> V -> Prop) (t e : V)
    (he : mem t e)
    (successors : forall x, mem t x -> exists y, Succ mem x y)
    (seed : Seed mem (fun x y => mem t x /\ Succ mem x y) e)
    (adjoin : forall C, exists I, mem t I /\
      forall z, mem t z -> (mem z I <-> z = e \/ mem z C)) :
  exists I, mem t I /\ mem e I /\
    forall x, mem t x -> mem x I ->
      exists y, mem t y /\ mem y I /\ Succ mem x y.
Proof.
  assert (range : forall x y, mem t x /\ Succ mem x y -> mem t y).
  { intros x y [Hx Hs]. exact (succ_tag Hx Hs). }
  assert (serial : forall x, mem t x -> exists y, mem t x /\ Succ mem x y).
  { intros x Hx. destruct (successors x Hx) as [y Hy]. exists y; now split. }
  destruct (seed_serial_container mem (fun x y => mem t x /\ Succ mem x y)
      (mem t) e he range serial seed) as [C [[s0 [[_ Hs0] Hs0C]] [tags next]]].
  destruct (adjoin C) as [I [HIt HI]]. exists I. split; [exact HIt|].
  split; [exact (proj2 (HI e he) (or_introl eq_refl))|].
  intros x Htx HxI. destruct (proj1 (HI x Htx) HxI) as [Hxe|HxC].
  - subst x. exists s0. split; [exact (succ_tag he Hs0)|].
    split; [|exact Hs0]. exact (proj2 (HI s0 (succ_tag he Hs0)) (or_intror Hs0C)).
  - destruct (next x HxC) as [y [[_ Hxy] HyC]]. exists y.
    split; [exact (tags y HyC)|]. split; [|exact Hxy].
    exact (proj2 (HI y (tags y HyC)) (or_intror HyC)).
Qed.

(** Equality in the tagged subtype is equality of underlying representatives.
    Lean's Subtype.ext uses built-in proof irrelevance. Here it is unnecessary:
    the equality relation relevant to the later quotient is made explicit. *)
Definition Tagged {V : Type} (mem : V -> V -> Prop) (t : V) := {x : V | mem t x}.
Definition tagged_mem {V : Type} {mem : V -> V -> Prop} {t : V}
    (x y : Tagged mem t) : Prop := mem (proj1_sig x) (proj1_sig y).
Definition tagged_eq {V : Type} {mem : V -> V -> Prop} {t : V}
    (x y : Tagged mem t) : Prop := proj1_sig x = proj1_sig y.

Theorem tagged_inductive {V : Type} {mem : V -> V -> Prop} {t e I : V}
    (he : mem t e) (hI : mem t I) (heI : mem e I)
    (hnext : forall x, mem t x -> mem x I ->
      exists y, mem t y /\ mem y I /\ Succ mem x y) :
  InductiveRel (@tagged_mem V mem t) (@tagged_eq V mem t)
    (exist _ e he) (exist _ I hI).
Proof.
  split; [exact heI|]. intros [x Htx] Hx.
  destruct (hnext x Htx Hx) as [y [Hty [HyI Hxy]]].
  exists (exist _ y Hty). split; [exact HyI|]. intros [z Htz]. exact (Hxy z).
Qed.

Definition QuotientPresentation {A B : Type}
    (raw : A -> A -> Prop) (mem : B -> B -> Prop) (q : A -> B) : Prop :=
  (forall b, exists a, q a = b) /\
  forall a b, mem (q a) (q b) <-> exists z, raw z b /\ q a = q z.

(** This more general version covers tagged representatives without assuming
    equality of their proof fields. [respect] is an explicit quotient-adapter
    obligation; it is not asserted as an axiom. Only reflexivity of E is used. *)
Theorem quotient_successor_rel {A B : Type}
    (raw : A -> A -> Prop) (mem : B -> B -> Prop) (E : A -> A -> Prop) (q : A -> B)
    (H : QuotientPresentation raw mem q)
    (refl : forall x, E x x) (respect : forall x y, E x y -> q x = q y)
    {x y : A} (hs : SuccRel raw E x y) : Succ mem (q x) (q y).
Proof.
  intro z. destruct H as [Hsurj Hmem]. destruct (Hsurj z) as [a <-].
  split.
  - intro Hz. destruct (proj1 (Hmem a y) Hz) as [b [Hb Hab]].
    destruct (proj1 (hs b) Hb) as [Hbx|Hbe].
    + left. apply (proj2 (Hmem a x)). exists b. now split.
    + right. exact (eq_trans Hab (respect b x Hbe)).
  - intros [Hax|Hax].
    + destruct (proj1 (Hmem a x) Hax) as [b [Hb Hab]].
      apply (proj2 (Hmem a y)). exists b.
      split; [exact (proj2 (hs b) (or_introl Hb))|exact Hab].
    + apply (proj2 (Hmem a y)). exists x.
      split; [exact (proj2 (hs x) (or_intror (refl x)))|exact Hax].
Qed.

Theorem quotient_successor {A B : Type}
    (raw : A -> A -> Prop) (mem : B -> B -> Prop) (q : A -> B)
    (H : QuotientPresentation raw mem q) {x y : A} (hs : Succ raw x y) :
  Succ mem (q x) (q y).
Proof.
  exact (quotient_successor_rel raw mem eq q H (fun _ => eq_refl)
    (fun _ _ h => f_equal q h) hs).
Qed.

Theorem quotient_infinity_rel {A B : Type}
    (raw : A -> A -> Prop) (mem : B -> B -> Prop) (E : A -> A -> Prop) (q : A -> B)
    (H : QuotientPresentation raw mem q)
    (refl : forall x, E x x) (respect : forall x y, E x y -> q x = q y)
    {e I : A} (hempty : forall z, ~ raw z e) (hI : InductiveRel raw E e I) :
  (forall z, ~ mem z (q e)) /\ InductiveSet mem (q e) (q I).
Proof.
  destruct H as [Hsurj Hmem]. split.
  - intros z Hz. destruct (Hsurj z) as [a <-].
    destruct (proj1 (Hmem a e) Hz) as [b [Hb _]]. exact (hempty b Hb).
  - split; [exact (proj2 (Hmem e I) (ex_intro _ e (conj (proj1 hI) eq_refl)))|].
    intros x Hx. destruct (Hsurj x) as [a <-].
    destruct (proj1 (Hmem a I) Hx) as [b [HbI Hab]].
    destruct (proj2 hI b HbI) as [c [HcI Hbc]]. exists (q c). split.
    + exact (proj2 (Hmem c I) (ex_intro _ c (conj HcI eq_refl))).
    + rewrite Hab. exact (quotient_successor_rel raw mem E q (conj Hsurj Hmem) refl respect Hbc).
Qed.

Theorem quotient_infinity {A B : Type}
    (raw : A -> A -> Prop) (mem : B -> B -> Prop) (q : A -> B)
    (H : QuotientPresentation raw mem q) {e I : A}
    (hempty : forall z, ~ raw z e) (hI : InductiveSet raw e I) :
  (forall z, ~ mem z (q e)) /\ InductiveSet mem (q e) (q I).
Proof.
  exact (quotient_infinity_rel raw mem eq q H (fun _ => eq_refl)
    (fun _ _ h => f_equal q h) hempty hI).
Qed.

Print Assumptions seed_serial_container.
Print Assumptions succ_tag.
Print Assumptions seed_tagged_container.
Print Assumptions tagged_inductive.
Print Assumptions quotient_successor_rel.
Print Assumptions quotient_successor.
Print Assumptions quotient_infinity_rel.
Print Assumptions quotient_infinity.
