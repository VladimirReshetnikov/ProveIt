(**
  Kripke-frame correspondences for the standard modal axioms.

  This ports the definability part of Foundation's
  [Modal/Kripke/AxiomGeach.lean] and [Modal/Kripke/AxiomPoint3.lean].

  There is an important constructive boundary.  Diamond is defined in the
  syntax as [~ box ~].  Producing a diamond from a concrete successor is
  constructive ([satisfies_dia_iter_intro]), while extracting a successor
  from a diamond uses classical logic ([satisfies_dia_iter_elim]).  The
  generic Geach result needs the latter in both directions.  Below, the
  standard forward validity lemmas are nevertheless proved directly, so
  T, D, B, Four, Five, Tc, and Point2 retain constructive proofs.  The
  atomic converses involving diamond, and both Point3 directions, are the
  explicitly classical part of this module.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Axioms Kripke.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The relational condition represented by a Geach tuple [(i,j,m,n)]. *)
Definition geach_convergent (F : frame) (g : geach_tuple) : Prop :=
  forall x y z : World F,
    rel_iter (Rel F) (geach_i g) x y ->
    rel_iter (Rel F) (geach_j g) x z ->
    exists u : World F,
      rel_iter (Rel F) (geach_m g) y u /\
      rel_iter (Rel F) (geach_n g) z u.

(** Generic validity.  This proof consumes an iterated diamond and therefore
    uses the classical elimination lemma from [Kripke]. *)
Lemma valid_Geach_of_geach_convergent :
  forall AtomType (F : frame) (g : geach_tuple)
         (p : formula AtomType),
    geach_convergent F g -> valid F (Geach g p).
Proof.
  intros AtomType F g p Hg V x Hantecedent.
  apply (proj2 (@satisfies_box_iter AtomType F V
    (geach_j g) x (dia_iter (geach_n g) p))).
  intros z Hxz.
  apply satisfies_dia_iter_intro.
  destruct (satisfies_dia_iter_elim Hantecedent)
    as [y [Hxy Hybox]].
  destruct (Hg x y z Hxy Hxz) as [u [Hyu Hzu]].
  exists u; split.
  - exact Hzu.
  - apply (proj1 (@satisfies_box_iter AtomType F V
      (geach_m g) y p) Hybox u Hyu).
Qed.

(** The truth-set valuation for atom zero recovers the relational condition.
    Witness extraction from the concluding diamond is classical. *)
Lemma geach_convergent_of_valid_Geach_atom :
  forall (F : frame) (g : geach_tuple),
    valid F (Geach g (Atom 0)) -> geach_convergent F g.
Proof.
  intros F g Hvalid x y z Hxy Hxz.
  pose (V := (fun _ u => rel_iter (Rel F) (geach_m g) y u)
    : valuation nat F).
  assert (Hantecedent :
    satisfies F V x
      (dia_iter (geach_i g) (box_iter (geach_m g) (Atom 0)))).
  {
    apply satisfies_dia_iter_intro.
    exists y; split.
    - exact Hxy.
    - apply (proj2 (@satisfies_box_iter nat F V
        (geach_m g) y (Atom 0))).
      intros u Hyu. exact Hyu.
  }
  pose proof (Hvalid V x) as Hconclusion.
  specialize (Hconclusion Hantecedent).
  pose proof (proj1 (@satisfies_box_iter nat F V
    (geach_j g) x (dia_iter (geach_n g) (Atom 0)))
    Hconclusion z Hxz) as Hz.
  destruct (satisfies_dia_iter_elim Hz) as [u [Hzu Hyu]].
  exists u; split; [exact Hyu | exact Hzu].
Qed.

Theorem valid_Geach_atom_iff_geach_convergent :
  forall (F : frame) (g : geach_tuple),
    valid F (Geach g (Atom 0)) <-> geach_convergent F g.
Proof.
  split.
  - intro Hvalid.
    exact (@geach_convergent_of_valid_Geach_atom F g Hvalid).
  - intro Hgeach.
    exact (@valid_Geach_of_geach_convergent nat F g (Atom 0) Hgeach).
Qed.

(** Named frame properties used by the standard instances of Geach's schema. *)

Definition frame_reflexive (F : frame) : Prop :=
  forall x : World F, Rel F x x.

Definition frame_serial (F : frame) : Prop :=
  forall x : World F, exists y : World F, Rel F x y.

Definition frame_symmetric (F : frame) : Prop :=
  forall x y : World F, Rel F x y -> Rel F y x.

Definition frame_transitive (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F y z -> Rel F x z.

Definition frame_right_euclidean (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F x z -> Rel F y z.

Definition frame_coreflexive (F : frame) : Prop :=
  forall x y : World F, Rel F x y -> x = y.

Definition frame_strongly_confluent (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F x z ->
    exists u : World F, Rel F y u /\ Rel F z u.

Definition frame_piecewise_strongly_connected (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F x z -> Rel F y z \/ Rel F z y.

(** T / reflexivity.  Both directions are constructive. *)

Lemma valid_T_of_reflexive :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_reflexive F -> valid F (T p).
Proof.
  intros AtomType F p Hrefl V x.
  change ((forall y, Rel F x y -> satisfies F V y p) ->
          satisfies F V x p).
  intro Hbox. apply Hbox. apply Hrefl.
Qed.

Lemma reflexive_of_valid_T :
  forall F : frame,
    valid F (T (Atom 0)) -> frame_reflexive F.
Proof.
  intros F Hvalid x.
  pose (V := (fun _ y => Rel F x y) : valuation nat F).
  pose proof (Hvalid V x) as HT.
  change ((forall y, Rel F x y -> V 0 y) -> V 0 x) in HT.
  apply HT. intros y Hxy. exact Hxy.
Qed.

Theorem valid_T_iff_reflexive :
  forall F : frame,
    valid F (T (Atom 0)) <-> frame_reflexive F.
Proof.
  split.
  - apply reflexive_of_valid_T.
  - intro Hrefl. exact (@valid_T_of_reflexive nat F (Atom 0) Hrefl).
Qed.

(** D / seriality.  The forward direction is constructive; the atomic
    converse extracts a successor from diamond and is classical. *)

Lemma valid_D_of_serial :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_serial F -> valid F (D p).
Proof.
  intros AtomType F p Hserial V x.
  change ((forall y, Rel F x y -> satisfies F V y p) ->
          satisfies F V x (Dia p)).
  intro Hbox.
  destruct (Hserial x) as [y Hxy].
  apply satisfies_dia_intro. exists y; split; auto.
Qed.

Lemma serial_of_valid_D :
  forall F : frame,
    valid F (D (Atom 0)) -> frame_serial F.
Proof.
  intros F Hvalid x.
  pose (V := (fun _ _ => True) : valuation nat F).
  assert (Hdia : satisfies F V x (Dia (Atom 0))).
  {
    apply (Hvalid V x). intros y Hxy. constructor.
  }
  destruct (@satisfies_dia_elim _ F V x _ Hdia) as [y [Hxy _]].
  now exists y.
Qed.

Theorem valid_D_iff_serial :
  forall F : frame,
    valid F (D (Atom 0)) <-> frame_serial F.
Proof.
  split.
  - apply serial_of_valid_D.
  - intro Hserial. exact (@valid_D_of_serial nat F (Atom 0) Hserial).
Qed.

(** B / symmetry.  The forward direction is constructive; the converse is
    classical because it extracts the predecessor witnessing diamond. *)

Lemma valid_B_of_symmetric :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_symmetric F -> valid F (B p).
Proof.
  intros AtomType F p Hsym V x.
  change (satisfies F V x p ->
          forall y, Rel F x y -> satisfies F V y (Dia p)).
  intros Hp y Hxy.
  apply satisfies_dia_intro. exists x; split; auto.
Qed.

Lemma symmetric_of_valid_B :
  forall F : frame,
    valid F (B (Atom 0)) -> frame_symmetric F.
Proof.
  intros F Hvalid x y Hxy.
  pose (V := (fun _ u => u = x) : valuation nat F).
  pose proof (Hvalid V x) as HB.
  change (V 0 x ->
          forall u, Rel F x u -> satisfies F V u (Dia (Atom 0))) in HB.
  specialize (HB eq_refl y Hxy).
  destruct (@satisfies_dia_elim _ F V y _ HB) as [u [Hyu Hu]].
  change (u = x) in Hu. now subst u.
Qed.

Theorem valid_B_iff_symmetric :
  forall F : frame,
    valid F (B (Atom 0)) <-> frame_symmetric F.
Proof.
  split.
  - apply symmetric_of_valid_B.
  - intro Hsym. exact (@valid_B_of_symmetric nat F (Atom 0) Hsym).
Qed.

(** Four / transitivity.  Both directions are constructive. *)

Lemma valid_Four_of_transitive :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_transitive F -> valid F (Four p).
Proof.
  intros AtomType F p Htrans V x.
  change ((forall y, Rel F x y -> satisfies F V y p) ->
          forall y, Rel F x y ->
          forall z, Rel F y z -> satisfies F V z p).
  intros Hbox y Hxy z Hyz.
  apply Hbox. eapply Htrans; eauto.
Qed.

Lemma transitive_of_valid_Four :
  forall F : frame,
    valid F (Four (Atom 0)) -> frame_transitive F.
Proof.
  intros F Hvalid x y z Hxy Hyz.
  pose (V := (fun _ u => Rel F x u) : valuation nat F).
  pose proof (Hvalid V x) as Hfour.
  unfold Four in Hfour; simpl in Hfour.
  assert (Hbb : satisfies F V x (Box (Box (Atom 0)))).
  {
    exact (Hfour (fun u Hxu => Hxu)).
  }
  specialize (Hbb y Hxy z Hyz). exact Hbb.
Qed.

Theorem valid_Four_iff_transitive :
  forall F : frame,
    valid F (Four (Atom 0)) <-> frame_transitive F.
Proof.
  split.
  - apply transitive_of_valid_Four.
  - intro Htrans.
    exact (@valid_Four_of_transitive nat F (Atom 0) Htrans).
Qed.

(** Five / right-Euclideanness.  The forward proof works directly with the
    negative definition of diamond and is constructive.  Its converse uses
    classical diamond elimination. *)

Lemma valid_Five_of_right_euclidean :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_right_euclidean F -> valid F (Five p).
Proof.
  intros AtomType F p Heucl V x Hdia y Hxy.
  unfold Dia, Neg in Hdia |- *; simpl in Hdia |- *.
  intro Hboxneg.
  apply Hdia. intros z Hxz Hzp.
  apply (Hboxneg z (Heucl x y z Hxy Hxz)). exact Hzp.
Qed.

Lemma right_euclidean_of_valid_Five :
  forall F : frame,
    valid F (Five (Atom 0)) -> frame_right_euclidean F.
Proof.
  intros F Hvalid x y z Hxy Hxz.
  pose (V := (fun _ u => u = z) : valuation nat F).
  assert (Hdiax : satisfies F V x (Dia (Atom 0))).
  {
    apply satisfies_dia_intro. exists z; split.
    - exact Hxz.
    - change (z = z). reflexivity.
  }
  pose proof (Hvalid V x) as Hfive.
  unfold Five in Hfive; simpl in Hfive.
  assert (Hboxdia : satisfies F V x (Box (Dia (Atom 0)))).
  {
    exact (Hfive Hdiax).
  }
  pose proof (Hboxdia y Hxy) as Hdiay.
  assert (Hexists : exists u, Rel F y u /\ V 0 u).
  {
    apply NNPP. intro Hnone.
    unfold Dia, Neg in Hdiay; simpl in Hdiay.
    apply Hdiay. intros u Hyu Hu.
    apply Hnone. now exists u.
  }
  destruct Hexists as [u [Hyu Hu]].
  change (u = z) in Hu. now subst u.
Qed.

Theorem valid_Five_iff_right_euclidean :
  forall F : frame,
    valid F (Five (Atom 0)) <-> frame_right_euclidean F.
Proof.
  split.
  - apply right_euclidean_of_valid_Five.
  - intro Heucl.
    exact (@valid_Five_of_right_euclidean nat F (Atom 0) Heucl).
Qed.

(** Tc / coreflexivity.  Both directions are constructive. *)

Lemma valid_Tc_of_coreflexive :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_coreflexive F -> valid F (Tc p).
Proof.
  intros AtomType F p Hcore V x Hp y Hxy.
  destruct (Hcore x y Hxy). exact Hp.
Qed.

Lemma coreflexive_of_valid_Tc :
  forall F : frame,
    valid F (Tc (Atom 0)) -> frame_coreflexive F.
Proof.
  intros F Hvalid x y Hxy.
  pose (V := (fun _ u => u = x) : valuation nat F).
  pose proof (Hvalid V x) as Htc.
  unfold Tc in Htc; simpl in Htc.
  assert (Hbox : satisfies F V x (Box (Atom 0))).
  {
    exact (Htc eq_refl).
  }
  specialize (Hbox y Hxy).
  change (y = x) in Hbox. symmetry; exact Hbox.
Qed.

Theorem valid_Tc_iff_coreflexive :
  forall F : frame,
    valid F (Tc (Atom 0)) <-> frame_coreflexive F.
Proof.
  split.
  - apply coreflexive_of_valid_Tc.
  - intro Hcore.
    exact (@valid_Tc_of_coreflexive nat F (Atom 0) Hcore).
Qed.

(** Point2 / local strong confluence.  The validity direction constructs
    diamond negatively and is constructive; the converse extracts its common
    successor classically. *)

Lemma valid_Point2_of_strong_confluence :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_strongly_confluent F -> valid F (Point2 p).
Proof.
  intros AtomType F p Hconf V x Hdia z Hxz.
  unfold Dia, Neg in Hdia |- *; simpl in Hdia |- *.
  intro Hboxneg.
  apply Hdia. intros y Hxy Hybox.
  destruct (Hconf x y z Hxy Hxz) as [u [Hyu Hzu]].
  apply (Hboxneg u Hzu). apply Hybox. exact Hyu.
Qed.

Lemma strong_confluence_of_valid_Point2 :
  forall F : frame,
    valid F (Point2 (Atom 0)) -> frame_strongly_confluent F.
Proof.
  intros F Hvalid x y z Hxy Hxz.
  pose (V := (fun _ u => Rel F y u) : valuation nat F).
  assert (Hdiabox : satisfies F V x (Dia (Box (Atom 0)))).
  {
    apply satisfies_dia_intro. exists y; split; [exact Hxy |].
    intros u Hyu. exact Hyu.
  }
  pose proof (Hvalid V x) as Hpoint2.
  unfold Point2 in Hpoint2; simpl in Hpoint2.
  assert (Hboxdia : satisfies F V x (Box (Dia (Atom 0)))).
  {
    exact (Hpoint2 Hdiabox).
  }
  pose proof (Hboxdia z Hxz) as Hdiaz.
  assert (Hexists : exists u, Rel F z u /\ V 0 u).
  {
    apply NNPP. intro Hnone.
    unfold Dia, Neg in Hdiaz; simpl in Hdiaz.
    apply Hdiaz. intros u Hzu Hu.
    apply Hnone. now exists u.
  }
  destruct Hexists as [u [Hzu Hyu]].
  exists u; split; [exact Hyu | exact Hzu].
Qed.

Theorem valid_Point2_iff_strong_confluence :
  forall F : frame,
    valid F (Point2 (Atom 0)) <-> frame_strongly_confluent F.
Proof.
  split.
  - apply strong_confluence_of_valid_Point2.
  - intro Hconf.
    exact (@valid_Point2_of_strong_confluence nat F (Atom 0) Hconf).
Qed.

(** Point3 / local strong connectedness.  The encoded disjunction is itself
    classical (material [Or]), so both directions intentionally use the
    classical semantic equivalence [satisfies_or]. *)

Lemma valid_Point3_of_piecewise_strong_connected :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_piecewise_strongly_connected F -> valid F (Point3 p q).
Proof.
  intros AtomType F p q Hconnected V x.
  unfold Point3.
  apply (proj2 (@satisfies_or AtomType F V x
    (Box (Imp (Box p) q)) (Box (Imp (Box q) p)))).
  apply NNPP. intro Hnone.
  assert (Hnotleft :
    ~ satisfies F V x (Box (Imp (Box p) q))).
  {
    intro Hleft. apply Hnone. now left.
  }
  assert (Hnotright :
    ~ satisfies F V x (Box (Imp (Box q) p))).
  {
    intro Hright. apply Hnone. now right.
  }
  assert (Hleftwitness :
    exists y, Rel F x y /\
      satisfies F V y (Box p) /\ ~ satisfies F V y q).
  {
    apply NNPP. intro Hmissing.
    apply Hnotleft. intros y Hxy Hybox.
    apply NNPP. intro Hnq.
    apply Hmissing. exists y; auto.
  }
  assert (Hrightwitness :
    exists z, Rel F x z /\
      satisfies F V z (Box q) /\ ~ satisfies F V z p).
  {
    apply NNPP. intro Hmissing.
    apply Hnotright. intros z Hxz Hzbox.
    apply NNPP. intro Hnp.
    apply Hmissing. exists z; auto.
  }
  destruct Hleftwitness as [y [Hxy [Hybox Hnqy]]].
  destruct Hrightwitness as [z [Hxz [Hzbox Hnpz]]].
  destruct (Hconnected x y z Hxy Hxz) as [Hyz | Hzy].
  - apply Hnpz. apply Hybox. exact Hyz.
  - apply Hnqy. apply Hzbox. exact Hzy.
Qed.

Lemma piecewise_strong_connected_of_valid_Point3 :
  forall F : frame,
    valid F (Point3 (Atom 0) (Atom 1)) ->
    frame_piecewise_strongly_connected F.
Proof.
  intros F Hvalid x y z Hxy Hxz.
  pose (V := (fun a u =>
      match a with
      | 0 => Rel F y u
      | 1 => Rel F z u
      | _ => False
      end) : valuation nat F).
  pose proof (Hvalid V x) as Hpoint.
  unfold Point3 in Hpoint.
  apply (proj1 (@satisfies_or nat F V x
    (Box (Imp (Box (Atom 0)) (Atom 1)))
    (Box (Imp (Box (Atom 1)) (Atom 0))))) in Hpoint.
  destruct Hpoint as [Hleft | Hright].
  - right.
    assert (Hybox : satisfies F V y (Box (Atom 0))).
    {
      intros u Hyu. exact Hyu.
    }
    specialize (Hleft y Hxy Hybox).
    exact Hleft.
  - left.
    assert (Hzbox : satisfies F V z (Box (Atom 1))).
    {
      intros u Hzu. exact Hzu.
    }
    specialize (Hright z Hxz Hzbox).
    exact Hright.
Qed.

Theorem valid_Point3_iff_piecewise_strong_connected :
  forall F : frame,
    valid F (Point3 (Atom 0) (Atom 1)) <->
    frame_piecewise_strongly_connected F.
Proof.
  split.
  - apply piecewise_strong_connected_of_valid_Point3.
  - intro Hconnected.
    exact (@valid_Point3_of_piecewise_strong_connected nat F
      (Atom 0) (Atom 1) Hconnected).
Qed.
