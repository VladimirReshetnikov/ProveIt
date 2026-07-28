(**
  Bisimulations, bounded morphisms, and modal invariance.

  This ports the reusable semantic results from
  Foundation/Modal/Kripke/Preservation.lean.  In particular, a bounded
  morphism need not be surjective; surjectivity is requested exactly where
  frame validity is transferred to its image.
*)

From FoundationModal Require Import Syntax Kripke Correspondence FrameProperties.

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

(** Two pointed models are modally equivalent when they agree on every
    formula.  Keeping this as an explicit predicate is useful independently
    of any particular bisimulation witness. *)
Definition modal_equivalent {AtomType : Type}
    {F1 : frame} (V1 : valuation AtomType F1) (x : World F1)
    {F2 : frame} (V2 : valuation AtomType F2) (y : World F2) : Prop :=
  forall p : formula AtomType,
    satisfies F1 V1 x p <-> satisfies F2 V2 y p.

Arguments modal_equivalent {AtomType F1} V1 x {F2} V2 y.

Lemma modal_equivalent_of_bisimilar :
  forall AtomType F1 F2 (V1 : valuation AtomType F1)
         (V2 : valuation AtomType F2)
         (Z : @bisimulation AtomType F1 V1 F2 V2) x y,
    bisimilar Z x y -> modal_equivalent V1 x V2 y.
Proof.
  intros AtomType F1 F2 V1 V2 Z x y Hxy p.
  exact (@bisimulation_invariance AtomType F1 F2 V1 V2 Z p x y Hxy).
Qed.

Lemma modal_equivalent_symmetry :
  forall AtomType F1 F2 (V1 : valuation AtomType F1)
         (V2 : valuation AtomType F2) x y,
    modal_equivalent V1 x V2 y -> modal_equivalent V2 y V1 x.
Proof.
  intros AtomType F1 F2 V1 V2 x y Heq p.
  symmetry. apply Heq.
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

(** A bounded morphism into a transitive frame extends along every nonempty
    finite path in its domain.  This is Foundation's
    [Frame.PseudoEpimorphism.TransitiveClosure]. *)
Definition p_morphism_transitive_closure {F1 F2 : frame}
    (f : @p_morphism F1 F2) (Htrans : frame_transitive F2)
    : @p_morphism (frame_trans_gen F1) F2.
Proof.
  refine {| pmap := fun x : World (frame_trans_gen F1) => pmap f x |}.
  - intros x y [n [Hn Hxy]].
    eapply rel_iter_collapse_of_transitive; eauto.
    exact (@p_morphism_forth_iter F1 F2 f n x y Hxy).
  - intros x z Hxz.
    destruct (@p_morphism_back F1 F2 f x z Hxz)
      as [y [Hy Hxy]].
    exists y; split; [exact Hy |].
    now apply positive_closure_base.
Defined.

Lemma p_morphism_rel_iff_of_injective :
  forall F1 F2 (f : @p_morphism F1 F2),
    (forall x y, pmap f x = pmap f y -> x = y) ->
    forall x y,
      Rel F2 (pmap f x) (pmap f y) <-> Rel F1 x y.
Proof.
  intros F1 F2 f Hinj x y; split.
  - intro Hxy.
    destruct (@p_morphism_back F1 F2 f x (pmap f y) Hxy)
      as [z [Hz Hxz]].
    now rewrite (Hinj z y Hz) in Hxz.
  - apply p_morphism_forth.
Qed.

Lemma p_morphism_rel_iter_iff_of_injective :
  forall F1 F2 (f : @p_morphism F1 F2),
    (forall x y, pmap f x = pmap f y -> x = y) ->
    forall n x y,
      rel_iter (Rel F2) n (pmap f x) (pmap f y) <->
      rel_iter (Rel F1) n x y.
Proof.
  intros F1 F2 f Hinj n x y; split.
  - intro Hxy.
    destruct (@p_morphism_back_iter F1 F2 f n x (pmap f y) Hxy)
      as [z [Hz Hxz]].
    now rewrite (Hinj z y Hz) in Hxz.
  - apply p_morphism_forth_iter.
Qed.

(** * Bounded morphisms between models *)

Record model_p_morphism {AtomType : Type}
    (F1 : frame) (V1 : valuation AtomType F1)
    (F2 : frame) (V2 : valuation AtomType F2) : Type := {
  model_p_morphism_frame : p_morphism F1 F2;
  model_p_morphism_atoms :
    forall a x,
      V1 a x <-> V2 a (pmap model_p_morphism_frame x)
}.

Arguments model_p_morphism AtomType F1 V1 F2 V2 : clear implicits.
Arguments model_p_morphism_frame
  {AtomType F1 V1 F2 V2} _.

Definition model_pmap {AtomType : Type}
    {F1 : frame} {V1 : valuation AtomType F1}
    {F2 : frame} {V2 : valuation AtomType F2}
    (f : model_p_morphism AtomType F1 V1 F2 V2)
    : World F1 -> World F2 :=
  pmap (model_p_morphism_frame f).

Arguments model_pmap {AtomType F1 V1 F2 V2} _ _.

Definition model_p_morphism_of_atomic {AtomType : Type}
    {F1 : frame} {V1 : valuation AtomType F1}
    {F2 : frame} {V2 : valuation AtomType F2}
    (f : p_morphism F1 F2)
    (Hatoms : forall a x, V1 a x <-> V2 a (pmap f x))
    : model_p_morphism AtomType F1 V1 F2 V2 :=
  {| model_p_morphism_frame := f;
     model_p_morphism_atoms := Hatoms |}.

Definition model_p_morphism_id {AtomType : Type}
    (F : frame) (V : valuation AtomType F)
    : model_p_morphism AtomType F V F V.
Proof.
  refine {| model_p_morphism_frame := p_morphism_id F |}.
  intros; reflexivity.
Defined.

Definition model_p_morphism_comp {AtomType : Type}
    {F1 : frame} {V1 : valuation AtomType F1}
    {F2 : frame} {V2 : valuation AtomType F2}
    {F3 : frame} {V3 : valuation AtomType F3}
    (f : model_p_morphism AtomType F1 V1 F2 V2)
    (g : model_p_morphism AtomType F2 V2 F3 V3)
    : model_p_morphism AtomType F1 V1 F3 V3.
Proof.
  refine
    {| model_p_morphism_frame :=
         p_morphism_comp (model_p_morphism_frame f)
           (model_p_morphism_frame g) |}.
  intros a x; simpl.
  transitivity (V2 a (model_pmap f x)).
  - apply model_p_morphism_atoms.
  - apply model_p_morphism_atoms.
Defined.

Definition model_p_morphism_bisimulation {AtomType : Type}
    {F1 : frame} {V1 : valuation AtomType F1}
    {F2 : frame} {V2 : valuation AtomType F2}
    (f : model_p_morphism AtomType F1 V1 F2 V2)
    : @bisimulation AtomType F1 V1 F2 V2.
Proof.
  refine {| bisimilar := fun x y => y = model_pmap f x |}.
  - intros x y a ->. apply model_p_morphism_atoms.
  - intros x y x' -> Hxx'.
    exists (model_pmap f x'); split; [reflexivity |].
    exact (p_morphism_forth (model_p_morphism_frame f) Hxx').
  - intros x y y' -> Hyy'.
    destruct (@p_morphism_back F1 F2 (model_p_morphism_frame f)
                x y' Hyy')
      as [x' [Hx' Hxx']].
    exists x'; split; [symmetry; exact Hx' | exact Hxx'].
Defined.

Theorem model_p_morphism_modal_equivalence :
  forall AtomType F1 (V1 : valuation AtomType F1)
         F2 (V2 : valuation AtomType F2)
         (f : model_p_morphism AtomType F1 V1 F2 V2) x,
    modal_equivalent V1 x V2 (model_pmap f x).
Proof.
  intros AtomType F1 V1 F2 V2 f x.
  apply (@modal_equivalent_of_bisimilar AtomType F1 F2 V1 V2
           (model_p_morphism_bisimulation f) x (model_pmap f x)).
  reflexivity.
Qed.

Theorem model_p_morphism_truth :
  forall AtomType F1 (V1 : valuation AtomType F1)
         F2 (V2 : valuation AtomType F2)
         (f : model_p_morphism AtomType F1 V1 F2 V2)
         x (p : formula AtomType),
    satisfies F1 V1 x p <-> satisfies F2 V2 (model_pmap f x) p.
Proof.
  intros. apply model_p_morphism_modal_equivalence.
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

(** Formula predicates are the semantic counterpart of Foundation's
    [FormulaSet]. *)
Definition validates_predicate {AtomType : Type}
    (F : frame) (T : formula AtomType -> Prop) : Prop :=
  forall p, T p -> valid F p.

Theorem validates_predicate_of_surjective_p_morphism :
  forall AtomType F1 F2 (f : @p_morphism F1 F2),
    (forall z, exists x, pmap f x = z) ->
    forall T : formula AtomType -> Prop,
      validates_predicate F1 T -> validates_predicate F2 T.
Proof.
  intros AtomType F1 F2 f Hsurj T Hvalid p Hp.
  eapply valid_of_surjective_p_morphism; eauto.
Qed.
