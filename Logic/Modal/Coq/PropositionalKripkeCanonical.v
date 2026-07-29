(** Canonical completeness for intuitionistic propositional Kripke semantics.

    Rather than reproduce Foundation's two-sided saturated tableaux, this
    module uses an enumerated maximal-theory construction relative to one
    avoided formula.  The finite-stage lemma for derivations is shared by
    deductive closure, primeness, the implication extension lemma, the truth
    lemma, and completeness. *)

From Stdlib Require Import Logic.ClassicalEpsilon Arith.PeanoNat.
From FoundationModal Require Import
  PropositionalFormula PropositionalEntailmentMinimal
  PropositionalHilbert PropositionalKripke.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pki_theory : Type := pformula nat -> Prop.

Definition pki_theory_included (T U : pki_theory) : Prop :=
  forall p, T p -> U p.

Definition pki_theory_empty : pki_theory := fun _ => False.

Definition pki_theory_insert (T : pki_theory) (p : pformula nat) :
    pki_theory := fun q => q = p \/ T q.

Definition pki_context (T : pki_theory) : pformula nat -> Type :=
  generic_proof_relevant_context T.

Definition pki_context_weaken {T U : pki_theory}
    (incl : pki_theory_included T U) :
    forall p, pki_context T p -> pki_context U p.
Proof.
  intros p [u Hp]. exists u. now apply incl.
Defined.

Definition pki_insert_context_to_adjoin (T : pki_theory)
    (p : pformula nat) : forall q,
    pki_context (pki_theory_insert T p) q ->
    generic_type_context_adjoin p (pki_context T) q.
Proof.
  intros q [u Hq].
  destruct (excluded_middle_informative (q = p)) as [-> | Hne].
  - exact GTCA_here.
  - apply GTCA_there. exists u. destruct Hq as [Heq | Hq].
    + contradiction.
    + exact Hq.
Defined.

Definition pki_derives (H : ph_hilbert nat) (T : pki_theory)
    (p : pformula nat) : Prop :=
  inhabited (ph_hilbert_type_context_proof H (pki_context T) p).

Lemma pki_derives_assumption :
  forall (H : ph_hilbert nat) T p, T p -> pki_derives H T p.
Proof.
  intros H T p Hp. constructor. apply GTCD_assumption.
  exists tt. exact Hp.
Qed.

Lemma pki_derives_theorem :
  forall (H : ph_hilbert nat) T p,
    ph_hilbert_provable H p -> pki_derives H T p.
Proof.
  intros H T p [d]. constructor. apply GTCD_theorem.
  change (ph_hilbert_proof H p). exact d.
Qed.

Lemma pki_derives_mdp :
  forall (H : ph_hilbert nat) T p q,
    pki_derives H T (PImp p q) ->
    pki_derives H T p -> pki_derives H T q.
Proof.
  intros H T p q [dpq] [dp]. constructor. exact (GTCD_mdp dpq dp).
Qed.

Lemma pki_derives_weaken :
  forall (H : ph_hilbert nat) T U,
    pki_theory_included T U -> forall p,
    pki_derives H T p -> pki_derives H U p.
Proof.
  intros H T U Hincl p [d]. constructor.
  exact (generic_type_context_derivation_weaken_raw
    (pki_context_weaken Hincl) d).
Qed.

Lemma pki_insert_included :
  forall T p, pki_theory_included T (pki_theory_insert T p).
Proof. intros T p q Hq. now right. Qed.

Lemma pki_derives_deduction :
  forall (H : ph_hilbert nat) T p q,
    pki_derives H (pki_theory_insert T p) q ->
    pki_derives H T (PImp p q).
Proof.
  intros H T p q [d]. constructor.
  apply ph_hilbert_type_context_deduction.
  eapply generic_type_context_derivation_weaken_raw; [|exact d].
  apply pki_insert_context_to_adjoin.
Qed.

Definition pki_nat_codec : pformula_atom_codec nat :=
  {| pformula_atom_encode := fun n => n;
     pformula_atom_decode := fun n => Some n;
     pformula_atom_decode_encode := fun _ => eq_refl |}.

Definition pki_step (H : ph_hilbert nat) (forbidden : pformula nat)
    (T : pki_theory) (p : pformula nat) : pki_theory :=
  if excluded_middle_informative
      (pki_derives H (pki_theory_insert T p) forbidden)
  then T else pki_theory_insert T p.

Fixpoint pki_chain (H : ph_hilbert nat) (forbidden : pformula nat)
    (seed : pki_theory) (n : nat) : pki_theory :=
  match n with
  | 0 => seed
  | S k => pki_step H forbidden (pki_chain H forbidden seed k)
      (pformula_enum pki_nat_codec k)
  end.

Definition pki_limit (H : ph_hilbert nat) (forbidden : pformula nat)
    (seed : pki_theory) : pki_theory :=
  fun p => exists n, pki_chain H forbidden seed n p.

Lemma pki_step_included :
  forall H forbidden T p,
    pki_theory_included T (pki_step H forbidden T p).
Proof.
  intros H forbidden T p q Hq. unfold pki_step.
  destruct (excluded_middle_informative
    (pki_derives H (pki_theory_insert T p) forbidden));
    [exact Hq | now right].
Qed.

Lemma pki_chain_succ_included :
  forall H forbidden seed n,
    pki_theory_included
      (pki_chain H forbidden seed n)
      (pki_chain H forbidden seed (S n)).
Proof. intros; apply pki_step_included. Qed.

Lemma pki_chain_included_of_le :
  forall H forbidden seed n m,
    n <= m -> pki_theory_included
      (pki_chain H forbidden seed n)
      (pki_chain H forbidden seed m).
Proof.
  intros H forbidden seed n m Hle; induction Hle.
  - intros p Hp; exact Hp.
  - intros p Hp. apply pki_chain_succ_included.
    now apply IHHle.
Qed.

Lemma pki_seed_included_limit :
  forall H forbidden seed,
    pki_theory_included seed (pki_limit H forbidden seed).
Proof. intros H forbidden seed p Hp. now exists 0. Qed.

Lemma pki_chain_avoids :
  forall H forbidden seed,
    ~ pki_derives H seed forbidden -> forall n,
    ~ pki_derives H (pki_chain H forbidden seed n) forbidden.
Proof.
  intros H forbidden seed Hseed n; induction n as [|n IH].
  - exact Hseed.
  - cbn [pki_chain]. unfold pki_step.
    destruct (excluded_middle_informative
      (pki_derives H
        (pki_theory_insert (pki_chain H forbidden seed n)
          (pformula_enum pki_nat_codec n)) forbidden)) as [Hbad | Hsafe].
    + exact IH.
    + exact Hsafe.
Qed.

(** Every derivation from the union uses assumptions from one finite stage. *)
Lemma pki_limit_derivation_stage_raw :
  forall H forbidden seed p,
    ph_hilbert_type_context_proof H
      (pki_context (pki_limit H forbidden seed)) p ->
    { n : nat &
      ph_hilbert_type_context_proof H
        (pki_context (pki_chain H forbidden seed n)) p }.
Proof.
  intros H forbidden seed p d; induction d as
      [p Hp | p d | p q dpq IHdpq dp IHdp].
  - destruct Hp as [u Hp].
    destruct (constructive_indefinite_description _ Hp) as [n Hn].
    exists n. apply GTCD_assumption. exists u. exact Hn.
  - exists 0. apply GTCD_theorem.
    change (ph_hilbert_proof H p). exact d.
  - destruct IHdpq as [n dn], IHdp as [m dm].
    exists (Nat.max n m).
    refine (@GTCD_mdp _ _ _ _ _ _ p q _ _).
    + eapply generic_type_context_derivation_weaken_raw; [|exact dn].
      apply pki_context_weaken, pki_chain_included_of_le, Nat.le_max_l.
    + eapply generic_type_context_derivation_weaken_raw; [|exact dm].
      apply pki_context_weaken, pki_chain_included_of_le, Nat.le_max_r.
Defined.

Lemma pki_limit_avoids :
  forall H forbidden seed,
    ~ pki_derives H seed forbidden ->
    ~ pki_derives H (pki_limit H forbidden seed) forbidden.
Proof.
  intros H forbidden seed Hseed [d].
  destruct (pki_limit_derivation_stage_raw d) as [n dn].
  apply (pki_chain_avoids (H := H) (forbidden := forbidden)
    (seed := seed) Hseed (n := n)). now constructor.
Qed.

Lemma pki_limit_maximal :
  forall H forbidden seed,
    ~ pki_derives H seed forbidden -> forall p,
    pki_limit H forbidden seed p \/
    pki_derives H
      (pki_theory_insert (pki_limit H forbidden seed) p) forbidden.
Proof.
  intros H forbidden seed Hseed p.
  destruct (pformula_enum_surjective pki_nat_codec p) as [n Henum].
  unfold pki_limit. subst p.
  cbn [pki_chain]. unfold pki_step.
  destruct (excluded_middle_informative
      (pki_derives H
        (pki_theory_insert (pki_chain H forbidden seed n)
          (pformula_enum pki_nat_codec n)) forbidden)) as [Hbad | Hsafe]
      eqn:Hdecision.
  - right. eapply pki_derives_weaken; [|exact Hbad].
    intros q [-> | Hq].
    + now left.
    + right. now exists n.
  - left. exists (S n). cbn [pki_chain]. unfold pki_step.
    rewrite Hdecision. exact (or_introl eq_refl).
Qed.

Lemma pki_limit_derivably_closed :
  forall H forbidden seed,
    ~ pki_derives H seed forbidden -> forall p,
    pki_derives H (pki_limit H forbidden seed) p ->
    pki_limit H forbidden seed p.
Proof.
  intros H forbidden seed Hseed p Hp.
  destruct (pki_limit_maximal Hseed p) as [Hmem | Hbad]; [exact Hmem |].
  exfalso. apply (pki_limit_avoids Hseed).
  eapply pki_derives_mdp.
  - exact (pki_derives_deduction (H := H)
      (T := pki_limit H forbidden seed) (p := p)
      (q := forbidden) Hbad).
  - exact Hp.
Qed.

Definition pki_has_efq (H : ph_hilbert nat) : Prop :=
  forall p, ph_hilbert_provable H (ph_axiom_efq p).

Record pki_prime_theory (H : ph_hilbert nat) : Type := {
  pki_prime_carrier : pki_theory;
  pki_prime_closed : forall p, pki_derives H pki_prime_carrier p ->
    pki_prime_carrier p;
  pki_prime_proper : ~ pki_prime_carrier PFalsum;
  pki_prime_or : forall p q,
    pki_prime_carrier (POr p q) ->
    pki_prime_carrier p \/ pki_prime_carrier q
}.

Definition pki_prime_mem {H} (T : pki_prime_theory H) : pki_theory :=
  pki_prime_carrier T.

Coercion pki_prime_mem : pki_prime_theory >-> pki_theory.

Theorem pki_prime_extension :
  forall H, pki_has_efq H -> forall seed forbidden,
    ~ pki_derives H seed forbidden ->
    { T : pki_prime_theory H |
      pki_theory_included seed T /\ ~ pki_prime_mem T forbidden }.
Proof.
  intros H Hefq seed forbidden Hseed.
  pose (L := pki_limit H forbidden seed).
  assert (Havoid : ~ pki_derives H L forbidden).
  { exact (pki_limit_avoids Hseed). }
  assert (Hclosed : forall p, pki_derives H L p -> L p).
  { exact (pki_limit_derivably_closed Hseed). }
  assert (Hproper : ~ L PFalsum).
  { intro Hbottom. apply Havoid.
    eapply pki_derives_mdp.
    - apply pki_derives_theorem, Hefq.
    - now apply pki_derives_assumption. }
  assert (Hor : forall p q, L (POr p q) -> L p \/ L q).
  { intros p q Hpq.
    destruct (classic (L p)) as [Hp | Hp]; [now left |].
    destruct (classic (L q)) as [Hq | Hq]; [now right |].
    exfalso.
    destruct (pki_limit_maximal Hseed p) as [Hpm | Hpf];
      [exact (Hp Hpm) |].
    destruct (pki_limit_maximal Hseed q) as [Hqm | Hqf];
      [exact (Hq Hqm) |].
    apply Havoid.
    apply (pki_derives_mdp
      (p := POr p q)
      (pki_derives_mdp
        (pki_derives_mdp
          (pki_derives_theorem (H := H)
            (p := ph_axiom_or3 p q forbidden)
            L (inhabits (PHPOrElim p q forbidden)))
          (pki_derives_deduction Hpf))
        (pki_derives_deduction Hqf))).
    now apply pki_derives_assumption. }
  exists {| pki_prime_carrier := L;
            pki_prime_closed := Hclosed;
            pki_prime_proper := Hproper;
            pki_prime_or := Hor |}.
  split.
  - apply pki_seed_included_limit.
  - intro Hmem. apply Havoid. now apply pki_derives_assumption.
Qed.

Lemma pki_prime_contains_theorems :
  forall H (T : pki_prime_theory H) p,
    ph_hilbert_provable H p -> pki_prime_mem T p.
Proof.
  intros H T p Hp. apply pki_prime_closed.
  now apply pki_derives_theorem.
Qed.

Lemma pki_prime_mdp :
  forall H (T : pki_prime_theory H) p q,
    pki_prime_mem T (PImp p q) -> pki_prime_mem T p ->
    pki_prime_mem T q.
Proof.
  intros H T p q Hpq Hp. apply pki_prime_closed.
  exact (pki_derives_mdp
    (pki_derives_assumption H (T := pki_prime_mem T)
      (p := PImp p q) Hpq)
    (pki_derives_assumption H (T := pki_prime_mem T)
      (p := p) Hp)).
Qed.

Lemma pki_prime_and_iff :
  forall H (T : pki_prime_theory H) p q,
    pki_prime_mem T (PAnd p q) <->
    pki_prime_mem T p /\ pki_prime_mem T q.
Proof.
  intros H T p q; split.
  - intro Hpq. split.
    + eapply pki_prime_mdp; [apply pki_prime_contains_theorems |exact Hpq].
      now constructor; apply PHPAndElimL.
    + eapply pki_prime_mdp; [apply pki_prime_contains_theorems |exact Hpq].
      now constructor; apply PHPAndElimR.
  - intros [Hp Hq].
    eapply pki_prime_mdp.
    + eapply pki_prime_mdp.
      * apply pki_prime_contains_theorems.
        now constructor; apply PHPAndIntro.
      * exact Hp.
    + exact Hq.
Qed.

Lemma pki_prime_or_iff :
  forall H (T : pki_prime_theory H) p q,
    pki_prime_mem T (POr p q) <->
    pki_prime_mem T p \/ pki_prime_mem T q.
Proof.
  intros H T p q; split.
  - apply pki_prime_or.
  - intros [Hp | Hq].
    + eapply pki_prime_mdp; [apply pki_prime_contains_theorems |exact Hp].
      now constructor; apply PHPOrIntroL.
    + eapply pki_prime_mdp; [apply pki_prime_contains_theorems |exact Hq].
      now constructor; apply PHPOrIntroR.
Qed.

Definition pki_canonical_frame (H : ph_hilbert nat) : pkripke_frame :=
  {| pkripke_world := pki_prime_theory H;
     pkripke_access := fun T U => pki_theory_included T U;
     pkripke_access_refl := fun _ p Hp => Hp;
     pkripke_access_trans := fun _ _ _ HTU HUV p Hp => HUV p (HTU p Hp) |}.

Definition pki_canonical_valuation (H : ph_hilbert nat) :
    pkripke_valuation nat (pki_canonical_frame H).
Proof.
  refine (@Build_pkripke_valuation nat (pki_canonical_frame H)
    (fun a T => pki_prime_mem T (PAtom a)) _).
  intros a T U HTU Ha. exact (HTU _ Ha).
Defined.

Definition pki_canonical_model (H : ph_hilbert nat) : pkripke_model nat :=
  {| pkripke_model_frame := pki_canonical_frame H;
     pkripke_model_valuation := pki_canonical_valuation H |}.

Lemma pki_prime_imp_forward :
  forall H (T U : pki_prime_theory H) p q,
    pki_prime_mem T (PImp p q) -> pki_theory_included T U ->
    pki_prime_mem U p -> pki_prime_mem U q.
Proof.
  intros H T U p q Hpq HTU Hp.
  exact (pki_prime_mdp (HTU _ Hpq) Hp).
Qed.

Lemma pki_prime_imp_counterextension :
  forall H, pki_has_efq H -> forall (T : pki_prime_theory H) p q,
    ~ pki_prime_mem T (PImp p q) ->
    { U : pki_prime_theory H |
      pki_theory_included T U /\ pki_prime_mem U p /\
      ~ pki_prime_mem U q }.
Proof.
  intros H Hefq T p q Hnot.
  assert (Havoid : ~ pki_derives H (pki_theory_insert T p) q).
  { intro Hd. apply Hnot, pki_prime_closed.
    now apply pki_derives_deduction. }
  destruct (pki_prime_extension Hefq Havoid) as [U [Hincl Hq]].
  exists U. repeat split.
  - intros r Hr. apply Hincl. now right.
  - apply Hincl. now left.
  - exact Hq.
Qed.

Theorem pki_canonical_truth_lemma :
  forall H, pki_has_efq H -> forall (T : pki_prime_theory H) p,
    pkripke_forces (pki_canonical_model H) T p <->
    pki_prime_mem T p.
Proof.
  intros H Hefq T p. revert T. induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq].
  - intro T. reflexivity.
  - intro T. cbn. split; [contradiction | apply pki_prime_proper].
  - intro T. cbn. rewrite IHp, IHq. symmetry. apply pki_prime_and_iff.
  - intro T. cbn. rewrite IHp, IHq. symmetry. apply pki_prime_or_iff.
  - intro T. cbn. split.
    + intro Hforce. apply NNPP. intro Hnot.
      destruct (pki_prime_imp_counterextension Hefq Hnot)
        as [U [HTU [Hp Hq]]].
      apply Hq, (proj1 (IHq U)).
      apply (Hforce U HTU), (proj2 (IHp U)), Hp.
    + intros Himp U HTU HUp.
      apply (proj2 (IHq U)).
      eapply pki_prime_imp_forward; [exact Himp |exact HTU |].
      now apply (proj1 (IHp U)).
Qed.

Fixpoint pki_empty_context_elim_raw (H : ph_hilbert nat) p
    (d : ph_hilbert_type_context_proof H
      (pki_context pki_theory_empty) p) :
    ph_hilbert_proof H p.
Proof.
  destruct d as [p Hp | p d | p q dpq dp].
  - destruct Hp as [u Hp]. exact (False_rect _ Hp).
  - exact d.
  - exact (PHPModusPonens
      (pki_empty_context_elim_raw H (PImp p q) dpq)
      (pki_empty_context_elim_raw H p dp)).
Defined.

Lemma pki_empty_derives_iff_provable :
  forall H p, pki_derives H pki_theory_empty p <->
    ph_hilbert_provable H p.
Proof.
  intros H p; split.
  - intros [d]. constructor. exact (pki_empty_context_elim_raw d).
  - apply pki_derives_theorem.
Qed.

Theorem pki_canonical_model_valid_iff_provable :
  forall H, pki_has_efq H -> forall p,
    pkripke_model_valid (pki_canonical_model H) p <->
    ph_hilbert_provable H p.
Proof.
  intros H Hefq p; split.
  - intro Hvalid. apply NNPP. intro Hnot.
    assert (Hseed : ~ pki_derives H pki_theory_empty p).
    { intro Hd. apply Hnot. now apply pki_empty_derives_iff_provable. }
    destruct (pki_prime_extension Hefq Hseed) as [T [_ Hnotmem]].
    apply Hnotmem, (proj1 (pki_canonical_truth_lemma Hefq T p)).
    exact (Hvalid T).
  - intros Hp T. apply (proj2 (pki_canonical_truth_lemma Hefq T p)).
    now apply pki_prime_contains_theorems.
Qed.

Definition pki_canonical_for_class (H : ph_hilbert nat)
    (C : pkripke_frame -> Prop) : Prop :=
  C (pki_canonical_frame H).

Theorem ph_hilbert_pkripke_complete_of_canonical :
  forall H, pki_has_efq H -> forall C,
    pki_canonical_for_class H C -> pkripke_complete H C.
Proof.
  intros H Hefq C Hcanonical p Hvalid.
  apply (proj1 (pki_canonical_model_valid_iff_provable Hefq p)).
  intro T. exact (Hvalid (pki_canonical_frame H) Hcanonical
    (pki_canonical_valuation H) T).
Qed.

Theorem ph_hilbert_pkripke_complete :
  forall H, pki_has_efq H ->
    pkripke_complete H (fun _ => True).
Proof.
  intros H Hefq. apply ph_hilbert_pkripke_complete_of_canonical.
  - exact Hefq.
  - exact I.
Qed.

(** Countermodel extraction is retained as a direct corollary of the same
    maximal-extension construction, useful independently of class validity. *)
Theorem pki_unprovable_has_canonical_countermodel :
  forall H, pki_has_efq H -> forall p,
    ~ ph_hilbert_provable H p ->
    exists T, ~ pkripke_forces (pki_canonical_model H) T p.
Proof.
  intros H Hefq p Hnot.
  assert (Hseed : ~ pki_derives H pki_theory_empty p).
  { intro Hd. apply Hnot. now apply pki_empty_derives_iff_provable. }
  destruct (pki_prime_extension Hefq Hseed) as [T [_ Hnotmem]].
  exists T. intro Hforce. apply Hnotmem.
  now apply (proj1 (pki_canonical_truth_lemma Hefq T p)).
Qed.

Definition pki_int_has_efq : pki_has_efq (ph_hilbert_int nat) :=
  fun p => inhabits (ph_hilbert_int_efq p).

Theorem ph_hilbert_int_pkripke_complete :
  pkripke_complete (ph_hilbert_int nat) (fun _ => True).
Proof. exact (ph_hilbert_pkripke_complete pki_int_has_efq). Qed.

Theorem ph_hilbert_int_pkripke_sound_complete :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_int nat) p <->
    pkripke_frame_class_valid (fun _ => True) p.
Proof.
  intro p; split.
  - apply ph_hilbert_int_pkripke_sound.
  - apply ph_hilbert_int_pkripke_complete.
Qed.
