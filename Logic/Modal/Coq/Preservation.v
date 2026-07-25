(**
  Bisimulations, bounded morphisms, and modal invariance.

  This ports the reusable semantic results from
  Foundation/Modal/Kripke/Preservation.lean.  In particular, a bounded
  morphism need not be surjective; surjectivity is requested exactly where
  frame validity is transferred to its image.
*)

From FoundationModal Require Import Syntax Kripke.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record bisimulation {AtomType : Type}
    (F1 : frame) (V1 : valuation AtomType F1)
    (F2 : frame) (V2 : valuation AtomType F2) : Type := {
  bisimilar : World F1 -> World F2 -> Prop;
  bisimulation_atoms :
    forall x y a, bisimilar x y -> (V1 a x <-> V2 a y);
  bisimulation_forth :
    forall x y x', bisimilar x y -> Rel F1 x x' ->
      exists y', bisimilar x' y' /\ Rel F2 y y';
  bisimulation_back :
    forall x y y', bisimilar x y -> Rel F2 y y' ->
      exists x', bisimilar x' y' /\ Rel F1 x x'
}.

Arguments bisimilar {AtomType F1 V1 F2 V2} _ _ _.

Definition bisimulation_symmetry {AtomType F1 F2}
    {V1 : valuation AtomType F1} {V2 : valuation AtomType F2}
    (Z : @bisimulation AtomType F1 V1 F2 V2)
    : @bisimulation AtomType F2 V2 F1 V1.
Proof.
  refine {| bisimilar := fun y x => bisimilar Z x y |}.
  - intros y x a Hxy. symmetry.
    exact (@bisimulation_atoms AtomType F1 V1 F2 V2 Z x y a Hxy).
  - intros y x y' Hxy Ryy'.
    destruct (@bisimulation_back AtomType F1 V1 F2 V2 Z
                x y y' Hxy Ryy') as [x' [Hx' Rxx']].
    exists x'; auto.
  - intros y x x' Hxy Rxx'.
    destruct (@bisimulation_forth AtomType F1 V1 F2 V2 Z
                x y x' Hxy Rxx') as [y' [Hy' Ryy']].
    exists y'; auto.
Defined.

Theorem bisimulation_invariance :
  forall AtomType F1 F2 (V1 : valuation AtomType F1)
         (V2 : valuation AtomType F2)
         (Z : @bisimulation AtomType F1 V1 F2 V2)
         (p : formula AtomType) x y,
    bisimilar Z x y ->
    (satisfies F1 V1 x p <-> satisfies F2 V2 y p).
Proof.
  intros AtomType F1 F2 V1 V2 Z p.
  induction p as [a| |p IHp q IHq|p IHp]; intros x y Hxy; simpl.
  - exact (@bisimulation_atoms AtomType F1 V1 F2 V2 Z x y a Hxy).
  - tauto.
  - rewrite (IHp x y Hxy), (IHq x y Hxy). reflexivity.
  - split; intros Hbox.
    + intros y' Ryy'.
      destruct (@bisimulation_back AtomType F1 V1 F2 V2 Z
                  x y y' Hxy Ryy') as [x' [Hx'y' Rxx']].
      apply (proj1 (IHp x' y' Hx'y')); auto.
    + intros x' Rxx'.
      destruct (@bisimulation_forth AtomType F1 V1 F2 V2 Z
                  x y x' Hxy Rxx') as [y' [Hx'y' Ryy']].
      apply (proj2 (IHp x' y' Hx'y')); auto.
Qed.

Record p_morphism (F1 F2 : frame) : Type := {
  pmap : World F1 -> World F2;
  p_morphism_forth :
    forall x y, Rel F1 x y -> Rel F2 (pmap x) (pmap y);
  p_morphism_back :
    forall x z, Rel F2 (pmap x) z ->
      exists y, pmap y = z /\ Rel F1 x y
}.

Arguments pmap {F1 F2} _ _.

Definition p_morphism_id (F : frame) : @p_morphism F F.
Proof.
  refine {| pmap := fun x => x |}; firstorder.
Defined.

Definition p_morphism_comp {F1 F2 F3}
    (f : @p_morphism F1 F2) (g : @p_morphism F2 F3)
    : @p_morphism F1 F3.
Proof.
  refine {| pmap := fun x => pmap g (pmap f x) |}.
  - intros x y Rxy.
    exact (@p_morphism_forth F2 F3 g (pmap f x) (pmap f y)
             (@p_morphism_forth F1 F2 f x y Rxy)).
  - intros x z Rxz.
    destruct (@p_morphism_back F2 F3 g (pmap f x) z Rxz)
      as [y [Hy Rfxy]].
    destruct (@p_morphism_back F1 F2 f x y Rfxy)
      as [u [Hu Rxu]].
    exists u; split; [now rewrite Hu, Hy | exact Rxu].
Defined.

Lemma p_morphism_forth_iter :
  forall F1 F2 (f : @p_morphism F1 F2) n x y,
    rel_iter (Rel F1) n x y ->
    rel_iter (Rel F2) n (pmap f x) (pmap f y).
Proof.
  intros F1 F2 f n; induction n as [|n IH]; intros x y Hxy; simpl in *.
  - now subst.
  - destruct Hxy as [z [Rxz Hzy]].
    exists (pmap f z); split.
    + exact (@p_morphism_forth F1 F2 f x z Rxz).
    + now apply IH.
Qed.

Lemma p_morphism_back_iter :
  forall F1 F2 (f : @p_morphism F1 F2) n x z,
    rel_iter (Rel F2) n (pmap f x) z ->
    exists y, pmap f y = z /\ rel_iter (Rel F1) n x y.
Proof.
  intros F1 F2 f n; induction n as [|n IH]; intros x z Hxz; simpl in *.
  - exists x; auto.
  - destruct Hxz as [u [Rxu Huz]].
    destruct (@p_morphism_back F1 F2 f x u Rxu) as [v [Hv Rxv]].
    subst u.
    destruct (IH v z Huz) as [y [Hy Hvy]].
    exists y; split; auto. exists v; auto.
Qed.

Definition pullback_valuation {AtomType F1 F2}
    (f : @p_morphism F1 F2) (V2 : valuation AtomType F2)
    : valuation AtomType F1 :=
  fun a x => V2 a (pmap f x).

Definition p_morphism_bisimulation {AtomType F1 F2}
    (f : @p_morphism F1 F2) (V2 : valuation AtomType F2)
    : @bisimulation AtomType F1 (pullback_valuation f V2) F2 V2.
Proof.
  refine {| bisimilar := fun x y => y = pmap f x |}.
  - intros x y a ->; reflexivity.
  - intros x y x' -> Rxx'.
    exists (pmap f x'); split; [reflexivity |].
    exact (@p_morphism_forth F1 F2 f x x' Rxx').
  - intros x y y' -> Ryy'.
    destruct (@p_morphism_back F1 F2 f x y' Ryy')
      as [x' [Hx' Rxx']].
    exists x'; split; [symmetry; exact Hx' | exact Rxx'].
Defined.

Theorem p_morphism_truth :
  forall AtomType F1 F2 (f : @p_morphism F1 F2)
         (V2 : valuation AtomType F2) x (p : formula AtomType),
    satisfies F1 (pullback_valuation f V2) x p <->
    satisfies F2 V2 (pmap f x) p.
Proof.
  intros.
  eapply bisimulation_invariance
    with (Z := p_morphism_bisimulation f V2).
  reflexivity.
Qed.

Theorem valid_of_surjective_p_morphism :
  forall AtomType F1 F2 (f : @p_morphism F1 F2),
    (forall z, exists x, pmap f x = z) ->
    forall p : formula AtomType, valid F1 p -> valid F2 p.
Proof.
  intros AtomType F1 F2 f Hsurj p Hvalid V2 z.
  destruct (Hsurj z) as [x Hx]; subst z.
  apply (proj1 (p_morphism_truth f V2 x p)).
  apply Hvalid.
Qed.
