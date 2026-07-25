(**
  Kripke correspondences for the weak confluence and weak connectedness
  axioms.

  This is an independent Coq port of the semantic theorem surfaces of the
  pinned Foundation modules [Modal/Kripke/AxiomWeakPoint2.lean] and
  [Modal/Kripke/AxiomWeakPoint3.lean].  The two source modules also install
  canonical-frame instances.  Those are dependency-gated on the extended
  Hilbert/canonical-model layer and are therefore not asserted here as
  semantic axioms.  Neither pinned source module contains an unfinished
  proof.

  As elsewhere in this development, diamond elimination and the classical
  disjunction encoding make the correspondence proofs classical.  The frame
  conditions themselves and their elementary interface lemmas introduce no
  additional assumptions.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Root FrameProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * WeakPoint2 / piecewise convergence *)

(** Foundation's [IsPiecewiseConvergent] is [frame_piecewise_convergent]
    from [Root]: distinct successors of one world have a common successor. *)

Lemma valid_WeakPoint2_of_piecewise_convergent :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_piecewise_convergent F -> valid F (WeakPoint2 p q).
Proof.
  intros AtomType F p q Hpiece V x Hantecedent.
  destruct (satisfies_dia_elim Hantecedent)
    as [y [Rxy Hy]].
  destruct (proj1 (@satisfies_and AtomType F V y (Box p) q) Hy)
    as [Hboxp Hqy].
  intros z Rxz.
  apply (proj2 (@satisfies_or AtomType F V z (Dia p) q)).
  destruct (classic (satisfies F V z q)) as [Hqz | Hnotqz].
  - now right.
  - left. apply satisfies_dia_intro.
    assert (Hyz : y <> z).
    { intro Hyz. subst z. contradiction. }
    destruct (Hpiece x y z Rxy Rxz Hyz) as [u [Ryu Rzu]].
    exists u; split; [exact Rzu | exact (Hboxp u Ryu)].
Qed.

Lemma piecewise_convergent_of_valid_WeakPoint2_atoms :
  forall F : frame,
    valid F (WeakPoint2 (Atom 0) (Atom 1)) ->
    frame_piecewise_convergent F.
Proof.
  intros F Hvalid x y z Rxy Rxz Hyz.
  pose (V := (fun a w =>
    match a with
    | 0 => Rel F y w
    | 1 => w = y
    | _ => False
    end) : valuation nat F).
  assert (Hantecedent :
    satisfies F V x (Dia (And (Box (Atom 0)) (Atom 1)))).
  {
    apply satisfies_dia_intro. exists y; split; [exact Rxy |].
    apply (proj2 (@satisfies_and nat F V y
      (Box (Atom 0)) (Atom 1))).
    split.
    - intros u Ryu. exact Ryu.
    - reflexivity.
  }
  pose proof (Hvalid V x Hantecedent z Rxz) as Hz.
  destruct (proj1 (@satisfies_or nat F V z
    (Dia (Atom 0)) (Atom 1)) Hz) as [Hdia | Hzy].
  - destruct (satisfies_dia_elim Hdia) as [u [Rzu Ryu]].
    exists u; auto.
  - exfalso. apply Hyz. now symmetry.
Qed.

Theorem valid_WeakPoint2_atoms_iff_piecewise_convergent :
  forall F : frame,
    valid F (WeakPoint2 (Atom 0) (Atom 1)) <->
    frame_piecewise_convergent F.
Proof.
  intro F; split.
  - apply piecewise_convergent_of_valid_WeakPoint2_atoms.
  - intro Hpiece.
    exact (@valid_WeakPoint2_of_piecewise_convergent
      nat F (Atom 0) (Atom 1) Hpiece).
Qed.

Corollary valid_WeakPoint2_of_piecewise_strongly_convergent :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_piecewise_strongly_convergent F -> valid F (WeakPoint2 p q).
Proof.
  intros AtomType F p q Hstrong.
  apply valid_WeakPoint2_of_piecewise_convergent.
  now apply piecewise_strongly_convergent_convergent.
Qed.

(** * WeakPoint3 / piecewise connectedness *)

(** This is the constructor [IsPiecewiseConnected.mk'] from Foundation: it
    is enough to compare distinct sibling successors. *)
Lemma frame_piecewise_connected_intro_distinct :
  forall F : frame,
    (forall x y z : World F,
      Rel F x y -> Rel F x z -> y <> z ->
      Rel F y z \/ Rel F z y) ->
    frame_piecewise_connected F.
Proof.
  intros F Hdistinct x y z Rxy Rxz.
  destruct (classic (y = z)) as [Hyz | Hyz].
  - now right; left.
  - destruct (Hdistinct x y z Rxy Rxz Hyz) as [Ryz | Rzy].
    + now left.
    + now right; right.
Qed.

Theorem frame_piecewise_connected_iff_distinct :
  forall F : frame,
    frame_piecewise_connected F <->
    forall x y z : World F,
      Rel F x y -> Rel F x z -> y <> z ->
      Rel F y z \/ Rel F z y.
Proof.
  intro F; split.
  - apply piecewise_connected_distinct.
  - apply frame_piecewise_connected_intro_distinct.
Qed.

Lemma valid_WeakPoint3_of_piecewise_connected :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_piecewise_connected F -> valid F (WeakPoint3 p q).
Proof.
  intros AtomType F p q Hpiece V x.
  apply (proj2 (@satisfies_or AtomType F V x
    (Box (Imp (Boxdot p) q))
    (Box (Imp (Boxdot q) p)))).
  destruct (classic
    (satisfies F V x (Box (Imp (Boxdot p) q))))
    as [Hleft | Hnotleft]; [now left | right].
  assert (Hex : exists y : World F,
      Rel F x y /\ satisfies F V y (Boxdot p) /\
      ~ satisfies F V y q).
  {
    apply NNPP. intro Hnone. apply Hnotleft.
    intros y Rxy Hboxdotp.
    apply NNPP. intro Hnotq. apply Hnone.
    exists y; auto.
  }
  destruct Hex as [y [Rxy [Hboxdotp Hnotqy]]].
  destruct (proj1 (@satisfies_and AtomType F V y p (Box p))
    Hboxdotp) as [Hpy Hboxp].
  intros z Rxz Hboxdotq.
  destruct (proj1 (@satisfies_and AtomType F V z q (Box q))
    Hboxdotq) as [Hqz Hboxq].
  destruct (Hpiece x y z Rxy Rxz) as [Ryz | [Hyz | Rzy]].
  - exact (Hboxp z Ryz).
  - now subst z.
  - exfalso. exact (Hnotqy (Hboxq y Rzy)).
Qed.

Lemma piecewise_connected_of_valid_WeakPoint3_atoms :
  forall F : frame,
    valid F (WeakPoint3 (Atom 0) (Atom 1)) ->
    frame_piecewise_connected F.
Proof.
  intros F Hvalid x y z Rxy Rxz.
  destruct (classic (Rel F y z \/ y = z \/ Rel F z y))
    as [Hconnected | Hnot]; [exact Hconnected |].
  exfalso.
  assert (Hnot_yz : ~ Rel F y z) by tauto.
  assert (Hneq : y <> z) by tauto.
  assert (Hnot_zy : ~ Rel F z y) by tauto.
  pose (V := (fun a w =>
    match a with
    | 0 => w = y \/ Rel F y w
    | 1 => w = z \/ Rel F z w
    | _ => True
    end) : valuation nat F).
  pose proof (Hvalid V x) as Hweak.
  destruct (proj1 (@satisfies_or nat F V x
    (Box (Imp (Boxdot (Atom 0)) (Atom 1)))
    (Box (Imp (Boxdot (Atom 1)) (Atom 0)))) Hweak)
    as [Hleft | Hright].
  - assert (Hboxdotp : satisfies F V y (Boxdot (Atom 0))).
    {
      apply (proj2 (@satisfies_and nat F V y
        (Atom 0) (Box (Atom 0)))).
      split.
      - now left.
      - intros u Ryu. now right.
    }
    pose proof (Hleft y Rxy Hboxdotp) as Hqy.
    destruct Hqy as [Hyz | Rzy]; contradiction.
  - assert (Hboxdotq : satisfies F V z (Boxdot (Atom 1))).
    {
      apply (proj2 (@satisfies_and nat F V z
        (Atom 1) (Box (Atom 1)))).
      split.
      - now left.
      - intros u Rzu. now right.
    }
    pose proof (Hright z Rxz Hboxdotq) as Hpz.
    destruct Hpz as [Hzy | Ryz].
    + apply Hneq. now symmetry.
    + contradiction.
Qed.

Theorem valid_WeakPoint3_atoms_iff_piecewise_connected :
  forall F : frame,
    valid F (WeakPoint3 (Atom 0) (Atom 1)) <->
    frame_piecewise_connected F.
Proof.
  intro F; split.
  - apply piecewise_connected_of_valid_WeakPoint3_atoms.
  - intro Hpiece.
    exact (@valid_WeakPoint3_of_piecewise_connected
      nat F (Atom 0) (Atom 1) Hpiece).
Qed.

Corollary valid_WeakPoint3_of_piecewise_strongly_connected :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_piecewise_strongly_connected F -> valid F (WeakPoint3 p q).
Proof.
  intros AtomType F p q Hstrong.
  apply valid_WeakPoint3_of_piecewise_connected.
  now apply piecewise_strongly_connected_connected.
Qed.
