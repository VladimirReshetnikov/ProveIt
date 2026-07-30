(** Setoid Heyting semantics for primitive propositional formulas.

    This ports Foundation/Propositional/Heyting/Semantics.lean.  Equality in
    Foundation's quotient-style algebras becomes the explicit equivalence of
    [heyting_algebra], so evaluation and soundness remain constructive and do
    not require quotient representatives or extensionality axioms. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  GenericSemantics PropositionalFormula PropositionalHilbert
  PropositionalEntailmentMinimal LindenbaumAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Small reusable Heyting-order toolkit *)

Definition pha_equiv {A : Type} (H : heyting_algebra A) : A -> A -> Prop :=
  gha_equiv (ha_generalized H).

Definition pha_le {A : Type} (H : heyting_algebra A) : A -> A -> Prop :=
  gha_le (ha_generalized H).

Definition pha_top {A : Type} (H : heyting_algebra A) : A :=
  gha_top (ha_generalized H).

Definition pha_bottom {A : Type} (H : heyting_algebra A) : A :=
  ha_bottom H.

Definition pha_meet {A : Type} (H : heyting_algebra A) : A -> A -> A :=
  gha_meet (ha_generalized H).

Definition pha_join {A : Type} (H : heyting_algebra A) : A -> A -> A :=
  gha_join (ha_generalized H).

Definition pha_imp {A : Type} (H : heyting_algebra A) : A -> A -> A :=
  gha_imp (ha_generalized H).

Definition pha_compl {A : Type} (H : heyting_algebra A) : A -> A :=
  ha_compl H.

Definition pheyting_formula_iff {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  PAnd (PImp p q) (PImp q p).

Lemma pha_equiv_refl : forall (A : Type) (H : heyting_algebra A) a,
  pha_equiv H a a.
Proof. intros; apply gha_equiv_refl. Qed.

Lemma pha_equiv_sym : forall (A : Type) (H : heyting_algebra A) a b,
  pha_equiv H a b -> pha_equiv H b a.
Proof. intros; now apply gha_equiv_sym. Qed.

Lemma pha_equiv_trans : forall (A : Type) (H : heyting_algebra A) a b c,
  pha_equiv H a b -> pha_equiv H b c -> pha_equiv H a c.
Proof. intros; eapply gha_equiv_trans; eauto. Qed.

Lemma pha_le_of_equiv : forall (A : Type) (H : heyting_algebra A) a b,
  pha_equiv H a b -> pha_le H a b.
Proof.
  intros A H a b Hab.
  apply (proj2 (@gha_le_respects_equiv A (ha_generalized H)
    a b b b Hab (@gha_equiv_refl A (ha_generalized H) b))).
  apply gha_le_refl.
Qed.

Lemma pha_le_of_equiv_sym : forall (A : Type) (H : heyting_algebra A) a b,
  pha_equiv H a b -> pha_le H b a.
Proof. intros; apply pha_le_of_equiv, pha_equiv_sym; assumption. Qed.

Lemma pha_equiv_of_le : forall (A : Type) (H : heyting_algebra A) a b,
  pha_le H a b -> pha_le H b a -> pha_equiv H a b.
Proof. intros; now apply gha_le_antisymmetric. Qed.

Lemma pha_meet_comm_le : forall (A : Type) (H : heyting_algebra A) a b,
  pha_le H (pha_meet H a b) (pha_meet H b a).
Proof.
  intros. apply gha_le_meet; [apply gha_meet_le_right | apply gha_meet_le_left].
Qed.

Lemma pha_order_mdp : forall (A : Type) (H : heyting_algebra A) x a b,
  pha_le H x (pha_imp H a b) -> pha_le H x a -> pha_le H x b.
Proof.
  intros A H x a b Himp Ha.
  eapply gha_le_trans.
  - apply gha_le_meet; [apply gha_le_refl | exact Ha].
  - apply (proj2 (@gha_imp_adjoint A (ha_generalized H) x a b)).
    exact Himp.
Qed.

Lemma pha_imp_top_iff_le : forall (A : Type) (H : heyting_algebra A) a b,
  pha_equiv H (pha_imp H a b) (pha_top H) <-> pha_le H a b.
Proof.
  intros A H a b; split.
  - intro Heq.
    assert (Htop : pha_le H (pha_top H) (pha_imp H a b)).
    { now apply pha_le_of_equiv_sym. }
    apply (proj2 (@gha_imp_adjoint A (ha_generalized H)
      (pha_top H) a b)) in Htop.
    eapply gha_le_trans.
    + apply gha_le_meet; [apply gha_le_top | apply gha_le_refl].
    + exact Htop.
  - intro Hab. apply gha_le_antisymmetric.
    + apply gha_le_top.
    + apply (proj1 (@gha_imp_adjoint A (ha_generalized H)
        (pha_top H) a b)).
      eapply gha_le_trans; [apply gha_meet_le_right | exact Hab].
Qed.

Lemma pha_meet_top_iff : forall (A : Type) (H : heyting_algebra A) a b,
  pha_equiv H (pha_meet H a b) (pha_top H) <->
  pha_equiv H a (pha_top H) /\ pha_equiv H b (pha_top H).
Proof.
  intros A H a b; split.
  - intro Hmeet. assert (Ht : pha_le H (pha_top H) (pha_meet H a b)).
    { now apply pha_le_of_equiv_sym. }
    split; apply gha_le_antisymmetric; [apply gha_le_top | | apply gha_le_top |].
    + eapply gha_le_trans; [exact Ht | apply gha_meet_le_left].
    + eapply gha_le_trans; [exact Ht | apply gha_meet_le_right].
  - intros [Ha Hb]. apply gha_le_antisymmetric; [apply gha_le_top |].
    apply gha_le_meet; now apply pha_le_of_equiv_sym.
Qed.

Lemma pha_bottom_not_top : forall (A : Type) (H : heyting_algebra A),
  (exists x y, ~ pha_equiv H x y) ->
  ~ pha_equiv H (pha_bottom H) (pha_top H).
Proof.
  intros A H [x [y Hxy]] Hbt. apply Hxy. apply gha_le_antisymmetric.
  - eapply gha_le_trans; [apply gha_le_top |].
    eapply gha_le_trans.
    + exact (@pha_le_of_equiv_sym A H (pha_bottom H) (pha_top H) Hbt).
    + apply ha_bottom_le.
  - eapply gha_le_trans; [apply gha_le_top |].
    eapply gha_le_trans.
    + exact (@pha_le_of_equiv_sym A H (pha_bottom H) (pha_top H) Hbt).
    + apply ha_bottom_le.
Qed.

Lemma pha_meet_join_cases : forall (A : Type) (H : heyting_algebra A)
    t p q r,
  pha_le H (pha_meet H t p) r ->
  pha_le H (pha_meet H t q) r ->
  pha_le H (pha_meet H t (pha_join H p q)) r.
Proof.
  intros A H t p q r Hp Hq.
  assert (Hpi : pha_le H p (pha_imp H t r)).
  { apply (proj1 (@gha_imp_adjoint A (ha_generalized H) p t r)).
    eapply gha_le_trans; [apply pha_meet_comm_le | exact Hp]. }
  assert (Hqi : pha_le H q (pha_imp H t r)).
  { apply (proj1 (@gha_imp_adjoint A (ha_generalized H) q t r)).
    eapply gha_le_trans; [apply pha_meet_comm_le | exact Hq]. }
  assert (Hjoin : pha_le H (pha_join H p q) (pha_imp H t r)).
  { now apply gha_join_le. }
  eapply gha_le_trans; [apply pha_meet_comm_le |].
  apply (proj2 (@gha_imp_adjoint A (ha_generalized H)
    (pha_join H p q) t r)).
  exact Hjoin.
Qed.

(** * Evaluation and algebraic models *)

Fixpoint pheyting_eval {Atom A : Type} (H : heyting_algebra A)
    (v : Atom -> A) (p : pformula Atom) : A :=
  match p with
  | PAtom a => v a
  | PFalsum => pha_bottom H
  | PAnd q r => pha_meet H (pheyting_eval H v q) (pheyting_eval H v r)
  | POr q r => pha_join H (pheyting_eval H v q) (pheyting_eval H v r)
  | PImp q r => pha_imp H (pheyting_eval H v q) (pheyting_eval H v r)
  end.

Lemma pheyting_eval_atom : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A) a, pheyting_eval H v (PAtom a) = v a.
Proof. reflexivity. Qed.

Lemma pheyting_eval_bottom : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A), pheyting_eval H v PFalsum = pha_bottom H.
Proof. reflexivity. Qed.

Lemma pheyting_eval_and : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A) p q,
  pheyting_eval H v (PAnd p q) =
  pha_meet H (pheyting_eval H v p) (pheyting_eval H v q).
Proof. reflexivity. Qed.

Lemma pheyting_eval_or : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A) p q,
  pheyting_eval H v (POr p q) =
  pha_join H (pheyting_eval H v p) (pheyting_eval H v q).
Proof. reflexivity. Qed.

Lemma pheyting_eval_imp : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A) p q,
  pheyting_eval H v (PImp p q) =
  pha_imp H (pheyting_eval H v p) (pheyting_eval H v q).
Proof. reflexivity. Qed.

Lemma pheyting_eval_top : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A),
  pha_equiv H (pheyting_eval H v ptop) (pha_top H).
Proof. intros; apply (proj2 (pha_imp_top_iff_le H _ _)), gha_le_refl. Qed.

Lemma pheyting_eval_neg : forall (Atom A : Type) (H : heyting_algebra A)
    (v : Atom -> A) p,
  pha_equiv H (pheyting_eval H v (pneg p))
    (pha_compl H (pheyting_eval H v p)).
Proof. intros; cbn; apply ha_imp_bottom. Qed.

Record pheyting_semantics (Atom : Type) : Type := {
  pheyting_carrier : Type;
  pheyting_algebra_of : heyting_algebra pheyting_carrier;
  pheyting_valuation : Atom -> pheyting_carrier;
  pheyting_nontrivial : exists x y,
    ~ pha_equiv pheyting_algebra_of x y
}.

Arguments pheyting_carrier {Atom} _.
Arguments pheyting_algebra_of {Atom} _.
Arguments pheyting_valuation {Atom} _ _.
Arguments pheyting_nontrivial {Atom} _.

Definition pheyting_value {Atom : Type} (S : pheyting_semantics Atom)
    (p : pformula Atom) : pheyting_carrier S :=
  pheyting_eval (pheyting_algebra_of S) (pheyting_valuation S) p.

Definition pheyting_satisfies {Atom : Type} (S : pheyting_semantics Atom)
    (p : pformula Atom) : Prop :=
  pha_equiv (pheyting_algebra_of S) (pheyting_value S p)
    (pha_top (pheyting_algebra_of S)).

Lemma pheyting_satisfies_imp_iff :
  forall (Atom : Type) (S : pheyting_semantics Atom) p q,
    pheyting_satisfies S (PImp p q) <->
    pha_le (pheyting_algebra_of S)
      (pheyting_value S p) (pheyting_value S q).
Proof. intros; apply pha_imp_top_iff_le. Qed.

Lemma pheyting_satisfies_and_iff :
  forall (Atom : Type) (S : pheyting_semantics Atom) p q,
    pheyting_satisfies S (PAnd p q) <->
    pheyting_satisfies S p /\ pheyting_satisfies S q.
Proof. intros; apply pha_meet_top_iff. Qed.

Lemma pheyting_satisfies_iff_iff :
  forall (Atom : Type) (S : pheyting_semantics Atom) p q,
    pheyting_satisfies S (pheyting_formula_iff p q) <->
    pha_equiv (pheyting_algebra_of S)
      (pheyting_value S p) (pheyting_value S q).
Proof.
  intros Atom S p q. unfold pheyting_formula_iff.
  rewrite pheyting_satisfies_and_iff,
    !pheyting_satisfies_imp_iff. split.
  - intros [Hpq Hqp]. now apply pha_equiv_of_le.
  - intro Heq. split; [now apply pha_le_of_equiv | now apply pha_le_of_equiv_sym].
Qed.

Lemma pheyting_satisfies_neg_iff :
  forall (Atom : Type) (S : pheyting_semantics Atom) p,
    pheyting_satisfies S (pneg p) <->
    pha_equiv (pheyting_algebra_of S)
      (pheyting_value S p) (pha_bottom (pheyting_algebra_of S)).
Proof.
  intros Atom S p. unfold pneg. rewrite pheyting_satisfies_imp_iff; split.
  - intro Hle. apply gha_le_antisymmetric; [exact Hle | apply ha_bottom_le].
  - intro Heq. now apply pha_le_of_equiv.
Qed.

Lemma pheyting_satisfies_top : forall (Atom : Type)
    (S : pheyting_semantics Atom), pheyting_satisfies S ptop.
Proof. intros; apply pheyting_eval_top. Qed.

Lemma pheyting_not_satisfies_bottom : forall (Atom : Type)
    (S : pheyting_semantics Atom), ~ pheyting_satisfies S PFalsum.
Proof. intros Atom S; apply pha_bottom_not_top, pheyting_nontrivial. Qed.

(** * Soundness of the primitive Minimal Hilbert calculus *)

Lemma pheyting_valid_K : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_K p q).
Proof.
  intros Atom S p q. unfold ph_axiom_K; cbn.
  rewrite pheyting_satisfies_imp_iff. cbn [pheyting_value].
  apply (proj1 (@gha_imp_adjoint _
    (ha_generalized (pheyting_algebra_of S)) _ _ _)).
  apply gha_meet_le_left.
Qed.

Lemma pheyting_valid_S : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q r,
  pheyting_satisfies S (ph_axiom_S p q r).
Proof.
  intros Atom S p q r. unfold ph_axiom_S; cbn.
  rewrite pheyting_satisfies_imp_iff. cbn [pheyting_value].
  set (H := pheyting_algebra_of S).
  set (a := pheyting_eval H (pheyting_valuation S) p).
  set (b := pheyting_eval H (pheyting_valuation S) q).
  set (c := pheyting_eval H (pheyting_valuation S) r).
  set (x := pha_imp H a (pha_imp H b c)).
  set (y := pha_imp H a b).
  apply (proj1 (@gha_imp_adjoint _ (ha_generalized H) x y
    (pha_imp H a c))).
  apply (proj1 (@gha_imp_adjoint _ (ha_generalized H)
    (pha_meet H x y) a c)).
  set (u := pha_meet H (pha_meet H x y) a).
  assert (Hux : pha_le H u x).
  { eapply gha_le_trans; [apply gha_meet_le_left | apply gha_meet_le_left]. }
  assert (Huy : pha_le H u y).
  { eapply gha_le_trans; [apply gha_meet_le_left | apply gha_meet_le_right]. }
  assert (Hua : pha_le H u a) by apply gha_meet_le_right.
  eapply pha_order_mdp with (a := b).
  - eapply pha_order_mdp with (a := a); eauto.
  - eapply pha_order_mdp with (a := a); eauto.
Qed.

Lemma pheyting_valid_and1 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_and1 p q).
Proof.
  intros. unfold ph_axiom_and1; cbn.
  rewrite pheyting_satisfies_imp_iff. apply gha_meet_le_left.
Qed.

Lemma pheyting_valid_and2 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_and2 p q).
Proof.
  intros. unfold ph_axiom_and2; cbn.
  rewrite pheyting_satisfies_imp_iff. apply gha_meet_le_right.
Qed.

Lemma pheyting_valid_and3 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_and3 p q).
Proof.
  intros Atom S p q. unfold ph_axiom_and3; cbn.
  rewrite pheyting_satisfies_imp_iff. cbn [pheyting_value].
  apply (proj1 (@gha_imp_adjoint _
    (ha_generalized (pheyting_algebra_of S)) _ _ _)).
  apply gha_le_refl.
Qed.

Lemma pheyting_valid_or1 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_or1 p q).
Proof.
  intros. unfold ph_axiom_or1; cbn.
  rewrite pheyting_satisfies_imp_iff. apply gha_le_join_left.
Qed.

Lemma pheyting_valid_or2 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (ph_axiom_or2 p q).
Proof.
  intros. unfold ph_axiom_or2; cbn.
  rewrite pheyting_satisfies_imp_iff. apply gha_le_join_right.
Qed.

Lemma pheyting_valid_or3 : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q r,
  pheyting_satisfies S (ph_axiom_or3 p q r).
Proof.
  intros Atom S p q r. unfold ph_axiom_or3; cbn.
  rewrite pheyting_satisfies_imp_iff. cbn [pheyting_value].
  set (H := pheyting_algebra_of S).
  set (a := pheyting_eval H (pheyting_valuation S) p).
  set (b := pheyting_eval H (pheyting_valuation S) q).
  set (c := pheyting_eval H (pheyting_valuation S) r).
  set (x := pha_imp H a c).
  set (y := pha_imp H b c).
  apply (proj1 (@gha_imp_adjoint _ (ha_generalized H) x y
    (pha_imp H (pha_join H a b) c))).
  apply (proj1 (@gha_imp_adjoint _ (ha_generalized H)
    (pha_meet H x y) (pha_join H a b) c)).
  apply pha_meet_join_cases.
  - apply pha_order_mdp with (a := a).
    + eapply gha_le_trans; [apply gha_meet_le_left | apply gha_meet_le_left].
    + apply gha_meet_le_right.
  - apply pha_order_mdp with (a := b).
    + eapply gha_le_trans; [apply gha_meet_le_left | apply gha_meet_le_right].
    + apply gha_meet_le_right.
Qed.

Lemma pheyting_valid_mdp : forall (Atom : Type)
    (S : pheyting_semantics Atom) p q,
  pheyting_satisfies S (PImp p q) -> pheyting_satisfies S p ->
  pheyting_satisfies S q.
Proof.
  intros Atom S p q Hpq Hp.
  apply pheyting_satisfies_imp_iff in Hpq.
  unfold pheyting_satisfies in *. apply gha_le_antisymmetric.
  - apply gha_le_top.
  - eapply gha_le_trans.
    + exact (@pha_le_of_equiv_sym _ (pheyting_algebra_of S)
        (pheyting_value S p) (pha_top (pheyting_algebra_of S)) Hp).
    + exact Hpq.
Qed.

Fixpoint pheyting_hilbert_proof_sound {Atom : Type} {H : ph_hilbert Atom}
    (S : pheyting_semantics Atom)
    (Hschema : forall p, ph_hilbert_schema H p -> pheyting_satisfies S p)
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    pheyting_satisfies S p.
Proof.
  destruct d.
  - now apply Hschema.
  - eapply pheyting_valid_mdp.
    + exact (@pheyting_hilbert_proof_sound Atom H S Hschema _ d1).
    + exact (@pheyting_hilbert_proof_sound Atom H S Hschema _ d2).
  - apply pheyting_satisfies_top.
  - apply pheyting_valid_S.
  - apply pheyting_valid_K.
  - apply pheyting_valid_and1.
  - apply pheyting_valid_and2.
  - apply pheyting_valid_and3.
  - apply pheyting_valid_or1.
  - apply pheyting_valid_or2.
  - apply pheyting_valid_or3.
Defined.

Definition pheyting_models_schema {Atom : Type} (H : ph_hilbert Atom)
    (S : pheyting_semantics Atom) : Prop :=
  forall p, ph_hilbert_schema H p -> pheyting_satisfies S p.

Definition pheyting_mod_valid {Atom : Type} (H : ph_hilbert Atom)
    (p : pformula Atom) : Prop :=
  forall S, pheyting_models_schema H S -> pheyting_satisfies S p.

Theorem pheyting_hilbert_sound :
  forall (Atom : Type) (H : ph_hilbert Atom) p,
    ph_hilbert_provable H p -> pheyting_mod_valid H p.
Proof.
  intros Atom H p [d] S HS.
  exact (@pheyting_hilbert_proof_sound Atom H S HS p d).
Qed.

(** * Quotient-free Lindenbaum model and completeness *)

Definition pheyting_intuitionistic {Atom : Type}
    (H : ph_hilbert Atom) : Type :=
  forall p, ph_hilbert_proof H (ph_axiom_efq p).

Definition pheyting_consistent {Atom : Type} (H : ph_hilbert Atom) : Prop :=
  ~ ph_hilbert_provable H PFalsum.

Definition ph_provable_raw {Atom : Type} {H : ph_hilbert Atom}
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    ph_hilbert_provable H p := inhabits d.

Definition pheyting_lindenbaum_laws {Atom : Type} (H : ph_hilbert Atom) :
  generic_lindenbaum_minimal_laws
    (pformula_connectives Atom) (ph_hilbert_provable H).
Proof.
  set (M := ph_hilbert_generic_minimal H).
  constructor.
  - intro p. exact (ph_provable_raw (generic_minimal_iff_refl_raw M p)).
  - intros p q [d]. exact (ph_provable_raw (generic_minimal_iff_symm_raw M p q d)).
  - intros p q r [d1] [d2].
    exact (ph_provable_raw (generic_minimal_iff_trans_raw M p q r d1 d2)).
  - intro p. exact (ph_provable_raw (generic_minimal_identity_raw M p)).
  - intros p q r [d1] [d2].
    exact (ph_provable_raw (generic_minimal_imp_trans_raw M p q r d1 d2)).
  - intros p q [d1] [d2].
    exact (ph_provable_raw (generic_minimal_iff_intro_raw M p q d1 d2)).
  - intros p p' q q' [dp] [dq]; split; intros [d].
    + pose (de := generic_minimal_imp_iff_congr_raw M p p' q q' dp dq).
      exact (ph_provable_raw (generic_minimal_mdp_raw M _ _
        (generic_minimal_iff_elim_left_raw M _ _ de) d)).
    + pose (de := generic_minimal_imp_iff_congr_raw M p p' q q' dp dq).
      exact (ph_provable_raw (generic_minimal_mdp_raw M _ _
        (generic_minimal_iff_elim_right_raw M _ _ de) d)).
  - intros p p' q q' [dp] [dq].
    exact (ph_provable_raw (generic_minimal_and_iff_congr_raw M
      p p' q q' dp dq)).
  - intros p p' q q' [dp] [dq].
    exact (ph_provable_raw (generic_minimal_or_iff_congr_raw M
      p p' q q' dp dq)).
  - intros p p' q q' [dp] [dq].
    exact (ph_provable_raw (generic_minimal_imp_iff_congr_raw M
      p p' q q' dp dq)).
  - intros p q [d].
    exact (ph_provable_raw (generic_minimal_neg_iff_congr_raw M p q d)).
  - intros p q. exact (ph_provable_raw (generic_minimal_and1 M p q)).
  - intros p q. exact (ph_provable_raw (generic_minimal_and2 M p q)).
  - intros p q r [d1] [d2].
    exact (ph_provable_raw (generic_minimal_right_and_intro_raw M
      p q r d1 d2)).
  - intros p q. exact (ph_provable_raw (generic_minimal_or1 M p q)).
  - intros p q. exact (ph_provable_raw (generic_minimal_or2 M p q)).
  - intros p q r [d1] [d2].
    exact (ph_provable_raw (generic_minimal_or_elim_raw M p q r d1 d2)).
  - intro p. exact (ph_provable_raw (generic_minimal_to_verum_raw M p)).
  - intros p q r; split; intros [d].
    + exact (ph_provable_raw (generic_minimal_curry_raw M p q r d)).
    + exact (ph_provable_raw (generic_minimal_uncurry_raw M p q r d)).
  - intro p; split.
    + intros [d]. apply ph_provable_raw.
      exact (generic_minimal_iff_intro_raw M p ptop
        (generic_minimal_to_verum_raw M p)
        (generic_minimal_dhyp_raw M p ptop d)).
    + intros [d]. apply ph_provable_raw.
      exact (generic_minimal_mdp_raw M _ _
        (generic_minimal_iff_elim_right_raw M _ _ d)
        (generic_minimal_verum M)).
Defined.

Definition pheyting_lindenbaum_int_laws {Atom : Type}
    (H : ph_hilbert Atom) (Hint : pheyting_intuitionistic H) :
  generic_lindenbaum_intuitionistic_laws
    (pformula_connectives Atom) (ph_hilbert_provable H).
Proof.
  constructor.
  - apply pheyting_lindenbaum_laws.
  - intro p. exact (ph_provable_raw (Hint p)).
  - intro p. exact (ph_provable_raw
      (generic_minimal_iff_refl_raw (ph_hilbert_generic_minimal H) (pneg p))).
Defined.

Definition pheyting_lindenbaum_model {Atom : Type}
    (H : ph_hilbert Atom) (Hint : pheyting_intuitionistic H)
    (Hcon : pheyting_consistent H) : pheyting_semantics Atom.
Proof.
  set (L := @pheyting_lindenbaum_int_laws Atom H Hint).
  refine {| pheyting_carrier := pformula Atom;
    pheyting_algebra_of := @generic_lindenbaum_heyting (pformula Atom)
      (pformula_connectives Atom) (ph_hilbert_provable H) L;
    pheyting_valuation := PAtom |}.
  exists PFalsum, ptop. intro Heq. apply Hcon.
  apply (proj2 (generic_lindenbaum_provable_iff_top
    (gli_minimal L) PFalsum)). exact Heq.
Defined.

Lemma pheyting_lindenbaum_value_eq :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Hint : pheyting_intuitionistic H) (Hcon : pheyting_consistent H) p,
    pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p = p.
Proof.
  intros Atom H Hint Hcon p; induction p; cbn [pheyting_value
    pheyting_lindenbaum_model pheyting_lindenbaum_int_laws
    generic_lindenbaum_heyting generic_lindenbaum_generalized_heyting
    pha_bottom pha_meet pha_join pha_imp].
  - reflexivity.
  - reflexivity.
  - change (PAnd
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p1)
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p2) =
      PAnd p1 p2). now rewrite IHp1, IHp2.
  - change (POr
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p1)
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p2) =
      POr p1 p2). now rewrite IHp1, IHp2.
  - change (PImp
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p1)
      (pheyting_value (@pheyting_lindenbaum_model Atom H Hint Hcon) p2) =
      PImp p1 p2). now rewrite IHp1, IHp2.
Qed.

Lemma pheyting_lindenbaum_satisfies_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Hint : pheyting_intuitionistic H) (Hcon : pheyting_consistent H) p,
    pheyting_satisfies (@pheyting_lindenbaum_model Atom H Hint Hcon) p <->
    ph_hilbert_provable H p.
Proof.
  intros Atom H Hint Hcon p. unfold pheyting_satisfies.
  rewrite pheyting_lindenbaum_value_eq.
  exact (iff_sym (generic_lindenbaum_provable_iff_top
    (@pheyting_lindenbaum_laws Atom H) p)).
Qed.

Theorem pheyting_hilbert_complete :
  forall (Atom : Type) (H : ph_hilbert Atom),
    pheyting_intuitionistic H -> forall p,
    pheyting_mod_valid H p -> ph_hilbert_provable H p.
Proof.
  intros Atom H Hint p Hvalid.
  destruct (classic (pheyting_consistent H)) as [Hcon | Hinc].
  - apply (proj1 (@pheyting_lindenbaum_satisfies_iff Atom H Hint Hcon p)).
    apply Hvalid. intros q Hq.
    apply (proj2 (@pheyting_lindenbaum_satisfies_iff Atom H Hint Hcon q)).
    now apply ph_hilbert_of_schema.
  - assert (Hbot : ph_hilbert_provable H PFalsum).
    { apply NNPP. exact Hinc. }
    destruct Hbot as [dbot]. apply ph_provable_raw.
    exact (PHPModusPonens (Hint p) dbot).
Qed.
