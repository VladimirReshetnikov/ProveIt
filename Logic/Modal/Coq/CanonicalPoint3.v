(**
  Canonical and finite completeness for K4.3 and S4.3.

  This module ports the complete theorem surfaces of the pinned Foundation
  files [Modal/Kripke/Logic/K4Point3.lean] and
  [Modal/Kripke/Logic/S4Point3.lean].  The calculi and their semantic frame
  classes were introduced by [CanonicalCombinations] and [Boxdot]; they are
  reused here rather than presented a second time.

  The canonical WeakPoint3 proof follows the upstream separating-formula
  argument.  If two distinct siblings are incomparable, each failed
  canonical relation supplies a boxed formula, while maximality supplies
  formulas separating the siblings in both directions.  Disjoining each
  boxed witness with the corresponding separator yields two stable Boxdot
  formulas, contradicting the two alternatives of WeakPoint3.
*)

From Stdlib Require Import
  Logic.Classical_Prop Logic.Classical_Pred_Type Lists.List.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence WeakCorrespondence Root
  Filtration FiltrationExtensions NormalHilbert CanonicalK
  CanonicalExtensions CanonicalDB5 CanonicalCombinations Boxdot
  CanonicalPoint2.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Substitution closure and finite frame classes *)

Lemma schema_Point3_substitution_closed :
  schema_substitution_closed schema_Point3.
Proof.
  intros A B sigma p [q [r ->]].
  exists (substitute sigma q), (substitute sigma r). reflexivity.
Qed.

Lemma S4Point3_schema_substitution_closed :
  schema_substitution_closed S4Point3_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact schema_Point3_substitution_closed.
Qed.

Definition S4Point3_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ S4Point3_frame_class F.

Definition S4Point3_linear_preorder_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\ frame_strongly_connected F.

Definition S4Point3_finite_linear_preorder_frame_class (F : frame) : Prop :=
  finite_frame F /\ S4Point3_linear_preorder_frame_class F.

(** * Atom-polymorphic soundness and consistency *)

Theorem S4Point3_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F ->
    frame_piecewise_strongly_connected F ->
    S4Point3_proves p -> valid F p.
Proof.
  intros AtomType F p HR HT HC Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Theorem K4Point3_is_consistent :
  forall AtomType, ~ @K4Point3_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := K4Point3_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
    + intros A p [q [r ->]].
      apply valid_WeakPoint3_of_piecewise_connected.
      intros [] [] [] _ _. now right; left.
Qed.

Theorem S4Point3_is_consistent :
  forall AtomType, ~ @S4Point3_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4Point3_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply schema_Point3_valid_on_piecewise_strongly_connected.
      intros [] [] [] _ _. now left.
Qed.

(** * Canonical support *)

Lemma normal_canonical_relation_failure :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    ~ @normal_canonical_relation Ax M N ->
    exists p,
      normal_mct_mem M (Box p) /\ normal_mct_mem N (Neg p).
Proof.
  intros Ax M N Hnot.
  unfold normal_canonical_relation in Hnot.
  apply not_all_ex_not in Hnot.
  destruct Hnot as [p Hp].
  exists p. split.
  - apply NNPP. intro Hnbox. apply Hp. now intros Hbox.
  - apply (proj2 (@normal_mct_neg_iff Ax N p)).
    intro Hmem. apply Hp. now intros _.
Qed.

Lemma normal_canonical_boxdot_or_left :
  forall Ax (M : normal_maximal_consistent_theory Ax) p d,
    normal_mct_mem M (Box p) -> normal_mct_mem M d ->
    satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax) M
      (Boxdot (Or p d)).
Proof.
  intros Ax M p d Hboxp Hd.
  apply (proj2 (@satisfies_and nat (normal_canonical_frame Ax)
    (@normal_canonical_valuation Ax) M (Or p d) (Box (Or p d)))).
  split.
  - apply (proj2 (@satisfies_or nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) M p d)).
    right. now apply (proj1 (@normal_canonical_truth_lemma Ax d M)).
  - intros N HMN.
    apply (proj2 (@satisfies_or nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) N p d)).
    left. apply (proj1 (@normal_canonical_truth_lemma Ax p N)).
    exact (HMN p Hboxp).
Qed.

Lemma normal_canonical_neg_or :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (Neg p) -> normal_mct_mem M (Neg q) ->
    satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax) M
      (Neg (Or p q)).
Proof.
  intros Ax M p q Hnp Hnq.
  change (satisfies (normal_canonical_frame Ax)
    (@normal_canonical_valuation Ax) M (Or p q) -> False).
  intro Hor.
  destruct (proj1 (@satisfies_or nat (normal_canonical_frame Ax)
    (@normal_canonical_valuation Ax) M p q) Hor) as [Hp | Hq].
  - exact (@normal_mct_not_both Ax M p
      (proj2 (@normal_canonical_truth_lemma Ax p M) Hp) Hnp).
  - exact (@normal_mct_not_both Ax M q
      (proj2 (@normal_canonical_truth_lemma Ax q M) Hq) Hnq).
Qed.

(** WeakPoint3 is canonical for every consistent normal extension containing
    all its substitution instances. *)
Theorem normal_canonical_piecewise_connected_of_schema_WeakPoint3 :
  forall Ax,
    schema_included K4Point3_weak_schema Ax ->
    frame_piecewise_connected (normal_canonical_frame Ax).
Proof.
  intros Ax HWeak M N O HMN HMO.
  destruct (classic (N = O)) as [-> | Hneq].
  - now right; left.
  - destruct (classic (@normal_canonical_relation Ax N O)) as [HNO | HnotNO].
    + now left.
    + right; right. apply NNPP. intro HnotON.
      destruct (@normal_canonical_relation_failure Ax N O HnotNO)
        as [a [HboxaN HnegaO]].
      destruct (@normal_canonical_relation_failure Ax O N HnotON)
        as [b [HboxbO HnegbN]].
      destruct (@normal_mct_separator Ax N O Hneq)
        as [d [HdN HnegdO]].
      assert (Hneq' : O <> N) by congruence.
      destruct (@normal_mct_separator Ax O N Hneq')
        as [e [HeO HnegeN]].
      pose (phi := Or a d).
      pose (psi := Or b e).
      assert (Haxiom : normal_mct_mem M (WeakPoint3 phi psi)).
      {
        apply normal_mct_derivable_mem. apply ND_theorem. apply Np_extra.
        apply HWeak. exists phi, psi. reflexivity.
      }
      pose proof (proj1 (@normal_canonical_truth_lemma Ax
        (WeakPoint3 phi psi) M) Haxiom) as Hsemantic.
      destruct (proj1 (@satisfies_or nat (normal_canonical_frame Ax)
        (@normal_canonical_valuation Ax) M
        (Box (Imp (Boxdot phi) psi))
        (Box (Imp (Boxdot psi) phi))) Hsemantic)
        as [Hleft | Hright].
      * assert (Hboxdot : satisfies (normal_canonical_frame Ax)
          (@normal_canonical_valuation Ax) N (Boxdot phi)).
        { unfold phi. now apply normal_canonical_boxdot_or_left. }
        pose proof (Hleft N HMN Hboxdot) as Hpsi.
        assert (Hnegpsi : satisfies (normal_canonical_frame Ax)
          (@normal_canonical_valuation Ax) N (Neg psi)).
        { unfold psi. now apply normal_canonical_neg_or. }
        exact (Hnegpsi Hpsi).
      * assert (Hboxdot : satisfies (normal_canonical_frame Ax)
          (@normal_canonical_valuation Ax) O (Boxdot psi)).
        { unfold psi. now apply normal_canonical_boxdot_or_left. }
        pose proof (Hright O HMO Hboxdot) as Hphi.
        assert (Hnegphi : satisfies (normal_canonical_frame Ax)
          (@normal_canonical_valuation Ax) O (Neg phi)).
        { unfold phi. now apply normal_canonical_neg_or. }
        exact (Hnegphi Hphi).
Qed.

Theorem normal_canonical_piecewise_strongly_connected_of_schema_Point3 :
  forall Ax,
    schema_included schema_Point3 Ax ->
    frame_piecewise_strongly_connected (normal_canonical_frame Ax).
Proof.
  intros Ax HPoint M N O HMN HMO.
  destruct (classic (@normal_canonical_relation Ax N O)) as [HNO | HnotNO].
  - now left.
  - right. apply NNPP. intro HnotON.
    destruct (@normal_canonical_relation_failure Ax N O HnotNO)
      as [a [HboxaN HnegaO]].
    destruct (@normal_canonical_relation_failure Ax O N HnotON)
      as [b [HboxbO HnegbN]].
    assert (Haxiom : normal_mct_mem M (Point3 a b)).
    {
      apply normal_mct_derivable_mem. apply ND_theorem. apply Np_extra.
      apply HPoint. exists a, b. reflexivity.
    }
    pose proof (proj1 (@normal_canonical_truth_lemma Ax (Point3 a b) M)
      Haxiom) as Hsemantic.
    destruct (proj1 (@satisfies_or nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) M
      (Box (Imp (Box a) b)) (Box (Imp (Box b) a))) Hsemantic)
      as [Hleft | Hright].
    + assert (Hboxa : satisfies (normal_canonical_frame Ax)
        (@normal_canonical_valuation Ax) N (Box a)).
      { now apply (proj1 (@normal_canonical_truth_lemma Ax (Box a) N)). }
      pose proof (Hleft N HMN Hboxa) as Hb.
      pose proof (proj1 (@normal_canonical_truth_lemma Ax (Neg b) N)
        HnegbN) as Hnb.
      exact (Hnb Hb).
    + assert (Hboxb : satisfies (normal_canonical_frame Ax)
        (@normal_canonical_valuation Ax) O (Box b)).
      { now apply (proj1 (@normal_canonical_truth_lemma Ax (Box b) O)). }
      pose proof (Hright O HMO Hboxb) as Ha.
      pose proof (proj1 (@normal_canonical_truth_lemma Ax (Neg a) O)
        HnegaO) as Hna.
      exact (Hna Ha).
Qed.

Lemma K4Point3_canonical_frame :
  K4Point3_frame_class (normal_canonical_frame K4Point3_schema).
Proof.
  split.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now left.
  - apply normal_canonical_piecewise_connected_of_schema_WeakPoint3.
    intros A p Hp. now right.
Qed.

Lemma S4Point3_canonical_frame :
  S4Point3_frame_class (normal_canonical_frame S4Point3_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. now right.
  - apply normal_canonical_piecewise_strongly_connected_of_schema_Point3.
    intros A p Hp. now right.
Qed.

(** * Ordinary and linear-preorder completeness *)

Theorem K4Point3_complete :
  forall p : formula nat,
    normal_valid_on_class K4Point3_frame_class p -> K4Point3_proves p.
Proof.
  unfold K4Point3_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := K4Point3_schema) (C := K4Point3_frame_class)).
  - exact (@K4Point3_is_consistent nat).
  - exact K4Point3_canonical_frame.
Qed.

Theorem S4Point3_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point3_frame_class p -> S4Point3_proves p.
Proof.
  unfold S4Point3_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point3_schema) (C := S4Point3_frame_class)).
  - exact (@S4Point3_is_consistent nat).
  - exact S4Point3_canonical_frame.
Qed.

Theorem K4Point3_sound_complete :
  forall p : formula nat,
    K4Point3_proves p <->
    normal_valid_on_class K4Point3_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HT HC]. now apply K4Point3_proves_sound_on_frame.
  - apply K4Point3_complete.
Qed.

Theorem S4Point3_sound_complete :
  forall p : formula nat,
    S4Point3_proves p <->
    normal_valid_on_class S4Point3_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HR [HT HC]]. now apply S4Point3_proves_sound_on_frame.
  - apply S4Point3_complete.
Qed.

Theorem S4Point3_linear_preorder_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point3_linear_preorder_frame_class p ->
    S4Point3_proves p.
Proof.
  intros p Hlinear. apply S4Point3_complete.
  intros F [HR [HT HC]] V r.
  apply (proj1 (@point_generated_truth_at_root nat F V r HT p)).
  apply (Hlinear (point_generated_frame F r)).
  repeat split.
  - now apply point_generated_reflexive.
  - now apply point_generated_transitive.
  - now apply point_generated_strongly_connected_of_piecewise.
Qed.

Theorem S4Point3_linear_preorder_sound :
  forall p : formula nat,
    S4Point3_proves p ->
    normal_valid_on_class S4Point3_linear_preorder_frame_class p.
Proof.
  intros p Hp F [HR [HT HC]].
  apply S4Point3_proves_sound_on_frame; try assumption.
  intros x y z _ _. exact (HC y z).
Qed.

Theorem S4Point3_linear_preorder_sound_complete :
  forall p : formula nat,
    S4Point3_proves p <->
    normal_valid_on_class S4Point3_linear_preorder_frame_class p.
Proof.
  intro p; split.
  - apply S4Point3_linear_preorder_sound.
  - apply S4Point3_linear_preorder_complete.
Qed.

(** * Finite-frame completeness *)

Lemma finest_tc_preserves_strongly_connected :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F) target,
    frame_strongly_connected F ->
    frame_strongly_connected
      (@finest_tc_filtered_frame AtomType F V target).
Proof.
  intros AtomType F V target HC X Y.
  destruct (HC (@representative AtomType F V target X)
               (@representative AtomType F V target Y))
    as [HXY | HYX].
  - left. apply positive_closure_single.
    exists (@representative AtomType F V target X),
      (@representative AtomType F V target Y).
    repeat split.
    + symmetry. apply representative_spec.
    + symmetry. apply representative_spec.
    + exact HXY.
  - right. apply positive_closure_single.
    exists (@representative AtomType F V target Y),
      (@representative AtomType F V target X).
    repeat split.
    + symmetry. apply representative_spec.
    + symmetry. apply representative_spec.
    + exact HYX.
Qed.

Theorem S4Point3_finite_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point3_finite_frame_class p ->
    S4Point3_proves p.
Proof.
  intros p Hfinite. apply S4Point3_complete.
  intros F [HR [HT HC]] V r.
  set (G := point_generated_frame F r).
  set (VG := point_generated_valuation V r).
  assert (HGreflexive : frame_reflexive G).
  { unfold G. now apply point_generated_reflexive. }
  assert (HGtransitive : frame_transitive G).
  { unfold G. now apply point_generated_transitive. }
  assert (HGconnected : frame_strongly_connected G).
  { unfold G. now apply point_generated_strongly_connected_of_piecewise. }
  pose (Q := @finest_tc_filtered_frame nat G VG p).
  pose (VQ := @finest_tc_filtered_valuation nat G VG p).
  assert (HQfinite : finite_frame Q).
  { unfold Q. apply finest_tc_filtered_frame_finite. }
  assert (HQreflexive : frame_reflexive Q).
  { unfold Q. now apply finest_tc_preserves_reflexive. }
  assert (HQtransitive : frame_transitive Q).
  { unfold Q. apply finest_tc_is_transitive. }
  assert (HQstrong : frame_strongly_connected Q).
  { unfold Q. now apply finest_tc_preserves_strongly_connected. }
  assert (HQpiece : frame_piecewise_strongly_connected Q).
  { intros x y z _ _. exact (HQstrong y z). }
  assert (HsatQ : satisfies Q VQ
    (@profile_class nat G VG p (point_generated_root F r)) p).
  {
    apply (Hfinite Q). repeat split; assumption.
  }
  apply (proj1 (@point_generated_truth_at_root nat F V r HT p)).
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat G VG p HGtransitive p (subformulas_self p)
    (point_generated_root F r))).
  exact HsatQ.
Qed.

Theorem S4Point3_finite_sound :
  forall p : formula nat,
    S4Point3_proves p ->
    normal_valid_on_class S4Point3_finite_frame_class p.
Proof.
  intros p Hp F [_ [HR [HT HC]]].
  now apply S4Point3_proves_sound_on_frame.
Qed.

Theorem S4Point3_finite_sound_complete :
  forall p : formula nat,
    S4Point3_proves p <->
    normal_valid_on_class S4Point3_finite_frame_class p.
Proof.
  intro p; split.
  - apply S4Point3_finite_sound.
  - apply S4Point3_finite_complete.
Qed.

(** * Frame-class and logic inclusions *)

Lemma S4Point3_frame_is_S4Point2 :
  forall F, S4Point3_frame_class F -> S4Point2_frame_class F.
Proof.
  intros F [HR [HT HC]]. repeat split; try assumption.
  now apply piecewise_strongly_connected_strongly_convergent_of_reflexive.
Qed.

Lemma S4Point3_frame_is_K4Point3 :
  forall F, S4Point3_frame_class F -> K4Point3_frame_class F.
Proof.
  intros F [_ [HT HC]]. split; [exact HT |].
  now apply piecewise_strongly_connected_connected.
Qed.

Lemma K4_weaker_than_K4Point3 :
  forall (AtomType : Type) (p : formula AtomType),
    K4_proves p -> K4Point3_proves p.
Proof.
  intros AtomType p Hp. unfold K4_proves, K4Point3_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma S4_weaker_than_S4Point3 :
  forall (AtomType : Type) (p : formula AtomType),
    S4_proves p -> S4Point3_proves p.
Proof.
  intros AtomType p Hp. unfold S4_proves, S4Point3_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma KT_weaker_than_S4Point3 :
  forall (AtomType : Type) (p : formula AtomType),
    KT_proves p -> S4Point3_proves p.
Proof.
  intros AtomType p Hp. apply S4_weaker_than_S4Point3.
  now apply KT_weaker_than_S4.
Qed.

Lemma S4Point2_weaker_than_S4Point3 :
  forall p : formula nat, S4Point2_proves p -> S4Point3_proves p.
Proof.
  intros p Hp. apply S4Point3_complete.
  intros F HF.
  destruct (S4Point3_frame_is_S4Point2 HF) as [HR [HT HC]].
  now apply S4Point2_proves_sound_on_frame.
Qed.

Lemma K4Point3_weaker_than_S4Point3 :
  forall p : formula nat, K4Point3_proves p -> S4Point3_proves p.
Proof.
  intros p Hp. apply S4Point3_complete.
  intros F HF.
  destruct (S4Point3_frame_is_K4Point3 HF) as [HT HC].
  now apply K4Point3_proves_sound_on_frame.
Qed.

(** * Explicit separating frames *)

Lemma point2_fork_not_piecewise_connected :
  ~ frame_piecewise_connected point2_fork_frame.
Proof.
  intro HC.
  destruct (HC W0 W1 W2 (or_introl eq_refl) (or_introl eq_refl))
    as [H12 | [Heq | H21]].
  - destruct H12 as [Hbad | Hbad]; discriminate.
  - discriminate.
  - destruct H21 as [Hbad | Hbad]; discriminate.
Qed.

Inductive point3_diamond_world : Type :=
| P30 | P31 | P32 | P33.

Definition point3_diamond_frame : frame :=
  {| World := point3_diamond_world;
     Rel := fun x y => x = y \/ x = P30 \/ y = P33 |}.

Lemma point3_diamond_reflexive :
  frame_reflexive point3_diamond_frame.
Proof. intro x. now left. Qed.

Lemma point3_diamond_transitive :
  frame_transitive point3_diamond_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [-> | [-> | ->]].
  - exact Hyz.
  - now right; left.
  - destruct Hyz as [Hyz | [Hbad | Hz]].
    + subst z. now right; right.
    + discriminate.
    + exact (or_intror (or_intror Hz)).
Qed.

Lemma point3_diamond_piecewise_strongly_convergent :
  frame_piecewise_strongly_convergent point3_diamond_frame.
Proof.
  intros x y z _ _. exists P33; split; now right; right.
Qed.

Lemma point3_diamond_not_piecewise_strongly_connected :
  ~ frame_piecewise_strongly_connected point3_diamond_frame.
Proof.
  intro HC.
  destruct (HC P30 P31 P32 (or_intror (or_introl eq_refl))
    (or_intror (or_introl eq_refl))) as [H12 | H21].
  - destruct H12 as [Hbad | [Hbad | Hbad]]; discriminate.
  - destruct H21 as [Hbad | [Hbad | Hbad]]; discriminate.
Qed.

Lemma one_way_frame_piecewise_connected_Point3 :
  frame_piecewise_connected one_way_frame.
Proof.
  intros x y z [_ Hy] [_ Hz]. right; left. congruence.
Qed.

Lemma one_way_frame_not_piecewise_strongly_connected_Point3 :
  ~ frame_piecewise_strongly_connected one_way_frame.
Proof.
  intro HC.
  destruct (HC DB0 DB1 DB1 (conj eq_refl eq_refl)
    (conj eq_refl eq_refl)) as [Hbad | Hbad];
    destruct Hbad as [Hbad _]; discriminate.
Qed.

(** * Strict inclusions *)

Theorem K4_strictly_weaker_K4Point3 :
  normal_strictly_weaker K4_proves K4Point3_proves.
Proof.
  split.
  - apply K4_weaker_than_K4Point3.
  - exists (WeakPoint3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HK4.
      pose proof (K4_proves_sound_on_transitive_frame
        point2_fork_transitive HK4) as Hvalid.
      apply point2_fork_not_piecewise_connected.
      now apply (proj1 (valid_WeakPoint3_atoms_iff_piecewise_connected
        point2_fork_frame)).
Qed.

Theorem S4Point2_strictly_weaker_S4Point3 :
  normal_strictly_weaker S4Point2_proves S4Point3_proves.
Proof.
  split.
  - exact S4Point2_weaker_than_S4Point3.
  - exists (Point3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HS4Point2.
      pose proof (S4Point2_proves_sound_on_frame
        point3_diamond_reflexive point3_diamond_transitive
        point3_diamond_piecewise_strongly_convergent HS4Point2) as Hvalid.
      apply point3_diamond_not_piecewise_strongly_connected.
      now apply (proj1 (valid_Point3_iff_piecewise_strong_connected
        point3_diamond_frame)).
Qed.

Theorem S4_strictly_weaker_S4Point3 :
  normal_strictly_weaker S4_proves S4Point3_proves.
Proof.
  split.
  - apply S4_weaker_than_S4Point3.
  - exists (Point3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HS4.
      pose proof (S4_proves_sound_on_preorder_frame
        point3_diamond_reflexive point3_diamond_transitive HS4) as Hvalid.
      apply point3_diamond_not_piecewise_strongly_connected.
      now apply (proj1 (valid_Point3_iff_piecewise_strong_connected
        point3_diamond_frame)).
Qed.

Theorem K4Point3_strictly_weaker_S4Point3 :
  normal_strictly_weaker K4Point3_proves S4Point3_proves.
Proof.
  split.
  - exact K4Point3_weaker_than_S4Point3.
  - exists (Point3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HK4Point3.
      pose proof (K4Point3_proves_sound_on_frame one_way_frame_transitive
        one_way_frame_piecewise_connected_Point3 HK4Point3) as Hvalid.
      apply one_way_frame_not_piecewise_strongly_connected_Point3.
      now apply (proj1 (valid_Point3_iff_piecewise_strong_connected
        one_way_frame)).
Qed.

Theorem KT_strictly_weaker_S4Point3 :
  normal_strictly_weaker KT_proves S4Point3_proves.
Proof.
  destruct KT_strictly_weaker_S4 as [HKT [p [HS4 HnotKT]]].
  split.
  - apply KT_weaker_than_S4Point3.
  - exists p; split.
    + now apply S4_weaker_than_S4Point3.
    + exact HnotKT.
Qed.
