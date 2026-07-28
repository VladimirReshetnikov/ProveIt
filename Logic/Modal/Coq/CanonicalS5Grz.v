(**
  The collapsed S5--Grzegorczyk logic.

  This file ports the theorem surfaces of the pinned Foundation modules

    - [Modal/Entailment/S5Grz.lean],
    - [Modal/Kripke/Logic/S5Grz.lean], and
    - the S5Grz/Triv declarations in [Modal/Hilbert/Normal/Basic.lean].

  Normal K is built into [normal_proves], so Foundation's four displayed
  generators K, T, Five, and Grz are represented by the additional schema

                     (T union Five) union Grz.

  The equivalence with Triv is proof-theoretic: each extra generator is
  translated into a derivation in the other calculus.  In particular, no
  completeness theorem for S5Grz and no prior S5Grz/Triv equivalence is used.
  The only completeness result used in the entailment argument is the
  already checked S5 theorem for the standard consequence
  [diamond (box p) -> box p].
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  NormalHilbert CanonicalExtensions FrameProperties LogicInfrastructure
  Modality Boxdot CanonicalS5 CanonicalTrivVer.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The concrete normal system *)

Definition S5Grz_schema : modal_axiom_schema :=
  schema_union S5_schema schema_Grz.

Definition S5Grz_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S5Grz_schema AtomType.

Lemma S5Grz_schema_substitution_closed :
  schema_substitution_closed S5Grz_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Five_substitution_closed.
  - exact schema_Grz_substitution_closed.
Qed.

Theorem S5Grz_proves_substitute :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    @S5Grz_proves A p ->
    @S5Grz_proves B (substitute sigma p).
Proof.
  intros A B sigma p Hp.
  exact (@normal_proves_substitute S5Grz_schema
    S5Grz_schema_substitution_closed A B sigma p Hp).
Qed.

Definition S5Grz_normal_logic : normal_logic (@S5Grz_proves nat) :=
  @normal_proves_logic_is_normal
    S5Grz_schema S5Grz_schema_substitution_closed.

Definition S5Grz_classical_logic : classical_logic (@S5Grz_proves nat) :=
  quasi_classical (normal_quasi S5Grz_normal_logic).

(** Direct introductions of the displayed generators. *)

Lemma S5Grz_proves_T :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves (T p).
Proof.
  intros AtomType p. apply Np_extra. left; left.
  exists p; reflexivity.
Qed.

Lemma S5Grz_proves_Five :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves (Five p).
Proof.
  intros AtomType p. apply Np_extra. left; right.
  exists p; reflexivity.
Qed.

Lemma S5Grz_proves_Grz :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves (Grz p).
Proof.
  intros AtomType p. apply Np_extra. right.
  exists p; reflexivity.
Qed.

Lemma S5_weaker_than_S5Grz :
  forall (AtomType : Type) (p : formula AtomType),
    S5_proves p -> S5Grz_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [|exact Hp].
  intros A q Hq. now left.
Qed.

Lemma Grz_weaker_than_S5Grz :
  forall (AtomType : Type) (p : formula AtomType),
    Grz_proves p -> S5Grz_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [|exact Hp].
  intros A q Hq. now right.
Qed.

(** * The S5Grz entailment consequence DiaT, and hence Tc *)

(** Foundation calls this S5 lemma [diabox_box].  Its short semantic proof
    is independent of Grz and of the target S5Grz/Triv equivalence. *)
Lemma S5_proves_dia_box_to_box :
  forall p : formula nat,
    S5_proves (Imp (Dia (Box p)) (Box p)).
Proof.
  intro p. apply S5_complete.
  intros F [Hrefl Heucl] V x Hdia.
  destruct (satisfies_dia_elim Hdia) as [y [Rxy Hybox]].
  intros z Rxz. apply Hybox with (u := z).
  exact (Heucl x y z Rxy Rxz).
Qed.

Lemma S5Grz_proves_dia_box_to_box :
  forall p : formula nat,
    S5Grz_proves (Imp (Dia (Box p)) (Box p)).
Proof.
  intros p. apply S5_weaker_than_S5Grz.
  exact (S5_proves_dia_box_to_box p).
Qed.

(** This is the source proof compressed through the repository's normal-
    logic combinators.  The middle implication is the boxed contraposition
    of [p -> box p]; Five supplies [diamond p -> box (diamond p)], and Grz
    discharges the resulting boxed fixed-point premise. *)
Lemma S5Grz_proves_DiaT_nat :
  forall p : formula nat,
    S5Grz_proves (DiaT p).
Proof.
  intro p.
  set (a := Box (Imp p (Box p))).
  set (b := Box (Neg (Box p))).
  set (c := Box (Neg p)).

  assert (Hcontra :
    S5Grz_proves
      (Imp (Imp p (Box p)) (Imp (Neg (Box p)) (Neg p)))).
  {
    apply (logic_classical_tautology S5Grz_classical_logic).
    intro rho. unfold Neg; simpl; tauto.
  }
  assert (Hboxed_contra :
    S5Grz_proves
      (Imp (Box (Imp p (Box p)))
        (Box (Imp (Neg (Box p)) (Neg p))))).
  {
    exact (logic_box_regularity S5Grz_normal_logic Hcontra).
  }
  assert (Hdistributed :
    S5Grz_proves (Imp a (Imp b c))).
  {
    unfold a, b, c.
    exact (logic_imp_trans S5Grz_classical_logic Hboxed_contra
      (quasi_modal_K (normal_quasi S5Grz_normal_logic)
        (Neg (Box p)) (Neg p))).
  }
  assert (Hdiamond_step :
    S5Grz_proves (Imp a (Imp (Dia p) (Dia (Box p))))).
  {
    assert (Hlift : S5Grz_proves
      (Imp (Imp a (Imp b c))
        (Imp a (Imp (Neg c) (Neg b))))).
    {
      apply (logic_classical_tautology S5Grz_classical_logic).
      intro rho. unfold Neg; simpl; tauto.
    }
    unfold Dia. exact (Np_mp Hlift Hdistributed).
  }
  assert (Hto_box :
    S5Grz_proves (Imp a (Imp (Dia p) (Box p)))).
  {
    assert (Hcompose : S5Grz_proves
      (Imp
        (Imp a (Imp (Dia p) (Dia (Box p))))
        (Imp
          (Imp (Dia (Box p)) (Box p))
          (Imp a (Imp (Dia p) (Box p)))))).
    {
      apply (logic_classical_tautology S5Grz_classical_logic).
      intro rho. simpl; tauto.
    }
    exact (Np_mp
      (Np_mp Hcompose Hdiamond_step)
      (S5Grz_proves_dia_box_to_box p)).
  }
  assert (Hto_plain :
    S5Grz_proves (Imp a (Imp (Dia p) p))).
  {
    assert (Hcompose : S5Grz_proves
      (Imp
        (Imp a (Imp (Dia p) (Box p)))
        (Imp (Imp (Box p) p) (Imp a (Imp (Dia p) p))))).
    {
      apply (logic_classical_tautology S5Grz_classical_logic).
      intro rho. simpl; tauto.
    }
    exact (Np_mp (Np_mp Hcompose Hto_box)
      (@S5Grz_proves_T nat p)).
  }
  assert (Hswapped :
    S5Grz_proves (Imp (Dia p) (Imp a p))).
  {
    assert (Hswap : S5Grz_proves
      (Imp (Imp a (Imp (Dia p) p))
        (Imp (Dia p) (Imp a p)))).
    {
      apply (logic_classical_tautology S5Grz_classical_logic).
      intro rho. simpl; tauto.
    }
    exact (Np_mp Hswap Hto_plain).
  }
  assert (Hboxed :
    S5Grz_proves (Imp (Box (Dia p)) (Box (Imp a p)))).
  {
    exact (logic_box_regularity S5Grz_normal_logic Hswapped).
  }
  assert (Hboxdia_to_plain :
    S5Grz_proves (Imp (Box (Dia p)) p)).
  {
    unfold a in Hboxed.
    exact (logic_imp_trans S5Grz_classical_logic Hboxed
      (@S5Grz_proves_Grz nat p)).
  }
  unfold DiaT.
  exact (logic_imp_trans S5Grz_classical_logic
    (@S5Grz_proves_Five nat p) Hboxdia_to_plain).
Qed.

(** The source entailment theorem is polymorphic.  The canonical layer's S5
    completeness API is over [nat], so polymorphism is recovered by proving
    the one-variable template and applying the already checked substitution
    theorem for the S5Grz schema. *)
Theorem S5Grz_proves_DiaT :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves (DiaT p).
Proof.
  intros AtomType p.
  pose proof (@normal_proves_substitute S5Grz_schema
    S5Grz_schema_substitution_closed nat AtomType
    (fun _ => p) (DiaT (Atom 0))
    (S5Grz_proves_DiaT_nat (Atom 0))) as H.
  simpl in H. exact H.
Qed.

(** Foundation packages DiaT as the equivalent presentation [KTc'].  The
    existing proof [KTc_prime_proves_Tc] performs exactly this classical
    conversion, so reaxiomatization transports it without duplicating the
    Hilbert derivation. *)
Theorem S5Grz_proves_Tc :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves (Tc p).
Proof.
  intros AtomType p.
  eapply (normal_proves_reaxiomatize
    (Ax := schema_DiaT) (Ay := S5Grz_schema)); [|].
  - intros A q [r ->]. apply S5Grz_proves_DiaT.
  - exact (@KTc_prime_proves_Tc AtomType p).
Qed.

Theorem KTc_weaker_than_S5Grz :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves p -> S5Grz_proves p.
Proof.
  intros AtomType p Hp.
  eapply (normal_proves_reaxiomatize
    (Ax := schema_Tc) (Ay := S5Grz_schema)); [|exact Hp].
  intros A q [r ->]. apply S5Grz_proves_Tc.
Qed.

(** * Direct soundness on Triv frames and consistency *)

Lemma Triv_frame_right_euclidean :
  forall F,
    Triv_kripke_frame_class F -> frame_right_euclidean F.
Proof.
  intros F [Hrefl Hcore] x y z Rxy Rxz.
  apply Hcore in Rxy. apply Hcore in Rxz.
  subst y; subst z. apply Hrefl.
Qed.

Lemma S5Grz_schema_valid_on_Triv_frame :
  forall F,
    Triv_kripke_frame_class F ->
    schema_valid_on_frame S5Grz_schema F.
Proof.
  intros F Htriv. unfold S5Grz_schema.
  apply schema_union_valid_on_frame.
  - unfold S5_schema. apply schema_union_valid_on_frame.
    + apply schema_T_valid_on_reflexive. exact (proj1 Htriv).
    + apply schema_Five_valid_on_right_euclidean.
      now apply Triv_frame_right_euclidean.
  - apply schema_Grz_valid_on_Grz_frame.
    + exact (proj1 Htriv).
    + now apply Triv_frame_transitive.
    + now apply Triv_frame_weak_cwf.
Qed.

Theorem S5Grz_proves_sound_on_Triv_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    Triv_kripke_frame_class F ->
    S5Grz_proves p -> valid F p.
Proof.
  intros AtomType F p Htriv Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  now apply S5Grz_schema_valid_on_Triv_frame.
Qed.

Theorem S5Grz_proves_sound_on_finite_Triv_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    finite_Triv_kripke_frame_class F ->
    S5Grz_proves p -> valid F p.
Proof.
  intros AtomType F p [_ Htriv].
  now apply S5Grz_proves_sound_on_Triv_frame.
Qed.

Theorem S5Grz_is_consistent :
  forall AtomType, ~ @S5Grz_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S5Grz_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply S5Grz_schema_valid_on_Triv_frame. split.
    + exact reflexive_singleton_reflexive.
    + exact reflexive_singleton_coreflexive.
Qed.

(** * Proof-theoretic collapse to Triv *)

Theorem S5Grz_weaker_than_Triv :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves p -> Triv_proves p.
Proof.
  intros AtomType p Hp.
  eapply (normal_proves_reaxiomatize
    (Ax := S5Grz_schema) (Ay := Triv_schema)); [|exact Hp].
  intros A q Hq. destruct Hq as [[[r ->] | [r ->]] | [r ->]].
  - apply Np_extra. left. exists r; reflexivity.
  - apply KTc_weaker_than_Triv. apply KTc_proves_Five.
  - apply Triv_proves_Grz.
Qed.

Theorem Triv_weaker_than_S5Grz :
  forall (AtomType : Type) (p : formula AtomType),
    Triv_proves p -> S5Grz_proves p.
Proof.
  intros AtomType p Hp.
  eapply (normal_proves_reaxiomatize
    (Ax := Triv_schema) (Ay := S5Grz_schema)); [|exact Hp].
  intros A q [[r ->] | [r ->]].
  - apply S5Grz_proves_T.
  - apply S5Grz_proves_Tc.
Qed.

Theorem S5Grz_Triv_provable_iff :
  forall (AtomType : Type) (p : formula AtomType),
    S5Grz_proves p <-> Triv_proves p.
Proof.
  intros AtomType p; split.
  - apply S5Grz_weaker_than_Triv.
  - apply Triv_weaker_than_S5Grz.
Qed.

(** The source's concrete-system equivalence.  Existing ordering APIs use
    formulas over [nat], so this record-shaped statement is its direct Coq
    counterpart; [S5Grz_Triv_provable_iff] retains the polymorphic form. *)
Theorem S5Grz_equiv_Triv :
  logic_equiv (@S5Grz_proves nat) (@Triv_proves nat).
Proof.
  split.
  - exact (@S5Grz_weaker_than_Triv nat).
  - exact (@Triv_weaker_than_S5Grz nat).
Qed.

(** This restates the requested finite-Triv soundness at the logic-set API.
    The proof remains direct and does not appeal to the equivalence above. *)
Theorem S5Grz_finite_Triv_sound :
  forall p : formula nat,
    S5Grz_proves p ->
    normal_valid_on_class finite_Triv_kripke_frame_class p.
Proof.
  intros p Hp F HF.
  now apply S5Grz_proves_sound_on_finite_Triv_frame.
Qed.

(** * Proper predecessors *)

Lemma trivver_all_reflexive_S5Grz :
  frame_reflexive trivver_all_frame.
Proof. intros []; exact trivver_true. Qed.

Lemma trivver_all_right_euclidean_S5Grz :
  frame_right_euclidean trivver_all_frame.
Proof. intros [] [] [] _ _; exact trivver_true. Qed.

Lemma trivver_all_not_antisymmetric_S5Grz :
  ~ frame_antisymmetric trivver_all_frame.
Proof.
  intro Hanti.
  specialize (Hanti TV0 TV1 trivver_true trivver_true).
  discriminate.
Qed.

Lemma S5_not_proves_Grz_atom :
  ~ S5_proves (Grz (Atom 0)).
Proof.
  intro Hp. apply trivver_all_not_antisymmetric_S5Grz.
  apply antisymmetric_of_valid_Grz_atom.
  exact (S5_proves_sound_on_reflexive_euclidean_frame
    trivver_all_reflexive_S5Grz
    trivver_all_right_euclidean_S5Grz Hp).
Qed.

Theorem S5_strictly_weaker_S5Grz :
  normal_strictly_weaker S5_proves S5Grz_proves.
Proof.
  split.
  - exact (@S5_weaker_than_S5Grz nat).
  - exists (Grz (Atom 0)); split.
    + apply S5Grz_proves_Grz.
    + exact S5_not_proves_Grz_atom.
Qed.

Lemma trivver_preorder_not_right_euclidean_S5Grz :
  ~ frame_right_euclidean trivver_preorder_frame.
Proof.
  intro Heucl.
  specialize (Heucl TV0 TV1 TV0 trivver_true trivver_true).
  exact Heucl.
Qed.

Lemma Grz_not_proves_Five_atom :
  ~ Grz_proves (Five (Atom 0)).
Proof.
  intro Hp. apply trivver_preorder_not_right_euclidean_S5Grz.
  apply (proj1 (valid_Five_iff_right_euclidean
    trivver_preorder_frame)).
  exact (Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame
    trivver_preorder_reflexive trivver_preorder_transitive
    trivver_preorder_weak_cwf Hp).
Qed.

Theorem Grz_strictly_weaker_S5Grz :
  normal_strictly_weaker Grz_proves S5Grz_proves.
Proof.
  split.
  - exact (@Grz_weaker_than_S5Grz nat).
  - exists (Five (Atom 0)); split.
    + apply S5Grz_proves_Five.
    + exact Grz_not_proves_Five_atom.
Qed.

(** Foundation derives this by the strict chain S4 < S5 < S5Grz = Triv.
    We retain the witness supplied by the already checked first strict step. *)
Theorem S4_strictly_weaker_Triv :
  normal_strictly_weaker S4_proves Triv_proves.
Proof.
  destruct S4_strictly_weaker_S5 as [HS4S5 [p [HS5 HnotS4]]].
  split.
  - intros q Hq. apply S5Grz_weaker_than_Triv.
    apply S5_weaker_than_S5Grz. now apply HS4S5.
  - exists p; split.
    + apply S5Grz_weaker_than_Triv.
      now apply S5_weaker_than_S5Grz.
    + exact HnotS4.
Qed.
