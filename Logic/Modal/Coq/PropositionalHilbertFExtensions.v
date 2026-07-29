(** Deduction and disjunction-property extensions for Hilbert F.

    This ports the complete active surface of
    Foundation/Propositional/Hilbert/F/Disjunctive and the independently
    proved portion of Hilbert/F/Deduction.  Finite support is generalized from
    finite sets requiring formula equality to duplicate-tolerant lists.  The
    source's list-conjunction deduction theorem contains two [sorry] blocks;
    it is not imported as an axiom. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalSlash
  PropositionalKripke2 PropositionalKripke2Correspondence
  PropositionalKripke2Hilbert.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Reusable inhabited-proof combinators *)

Lemma phf_provable_mdp :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H (PImp p q) -> phf_provable H p ->
    phf_provable H q.
Proof.
  intros Atom H p q [Hpq] [Hp]. constructor.
  exact (PHFPModusPonens Hpq Hp).
Qed.

Lemma phf_provable_afortiori :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H p -> phf_provable H (PImp q p).
Proof.
  intros Atom H p q [Hp]. constructor. exact (PHFPAFortiori q Hp).
Qed.

Lemma phf_provable_and_rule :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H p -> phf_provable H q ->
    phf_provable H (PAnd p q).
Proof.
  intros Atom H p q [Hp] [Hq]. constructor. exact (PHFPAndRule Hp Hq).
Qed.

Lemma phf_provable_or_left :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H p -> phf_provable H (POr p q).
Proof.
  intros Atom H p q [Hp]. constructor.
  exact (PHFPModusPonens (PHFPOrIntroL p q) Hp).
Qed.

Lemma phf_provable_or_right :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H q -> phf_provable H (POr p q).
Proof.
  intros Atom H p q [Hq]. constructor.
  exact (PHFPModusPonens (PHFPOrIntroR p q) Hq).
Qed.

Lemma phf_provable_imp_trans :
  forall (Atom : Type) (H : phf_hilbert Atom) p q r,
    phf_provable H (PImp p q) -> phf_provable H (PImp q r) ->
    phf_provable H (PImp p r).
Proof.
  intros Atom H p q r [Hpq] [Hqr]. constructor.
  exact (PHFPModusPonens (PHFPAxiomI p q r) (PHFPAndRule Hpq Hqr)).
Qed.

Lemma phf_provable_imp_and :
  forall (Atom : Type) (H : phf_hilbert Atom) p q r,
    phf_provable H (PImp p q) -> phf_provable H (PImp p r) ->
    phf_provable H (PImp p (PAnd q r)).
Proof.
  intros Atom H p q r [Hpq] [Hpr]. constructor.
  exact (PHFPModusPonens (PHFPAxiomC p q r) (PHFPAndRule Hpq Hpr)).
Qed.

(** * Aczel slash and disjunctivity *)

Theorem phf_provable_of_aczel_slash :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    p_aczel_slash (phf_provable H) p -> phf_provable H p.
Proof.
  intros Atom H p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; cbn.
  - exact (fun H => H).
  - contradiction.
  - intros [Hp Hq]. now apply phf_provable_and_rule; auto.
  - intros [Hp | Hq].
    + now apply phf_provable_or_left, IHp.
    + now apply phf_provable_or_right, IHq.
  - intros [Hpq _]. exact Hpq.
Qed.

Theorem phf_aczel_slash_of_proof :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    phf_proof H p ->
    (forall q, phf_schema H q ->
      p_aczel_slash (phf_provable H) q) ->
    p_aczel_slash (phf_provable H) p.
Proof.
  intros Atom H p d; induction d; intro Hschema.
  - now apply Hschema.
  - split.
    + constructor. apply PHFPAndElimL.
    + intros [Hp _]. exact Hp.
  - split.
    + constructor. apply PHFPAndElimR.
    + intros [_ Hq]. exact Hq.
  - split.
    + constructor. apply PHFPOrIntroL.
    + now intros Hp; left.
  - split.
    + constructor. apply PHFPOrIntroR.
    + now intros Hq; right.
  - split.
    + constructor. apply PHFPDistributeAndOr.
    + intros [Hp [Hq | Hr]].
      * left; now split.
      * right; now split.
  - split.
    + constructor. apply PHFPAxiomC.
    + intros [[Hpq Hpqf] [Hpr Hprf]]. split.
      * now apply phf_provable_imp_and.
      * intro Hp; split; [now apply Hpqf | now apply Hprf].
  - split.
    + constructor. apply PHFPAxiomD.
    + intros [[Hpr Hprf] [Hqr Hqrf]]. split.
      * destruct Hpr as [dpr]; destruct Hqr as [dqr]. constructor.
        exact (PHFPModusPonens (PHFPAxiomD _ _ _)
          (PHFPAndRule dpr dqr)).
      * intros [Hp | Hq]; [now apply Hprf | now apply Hqrf].
  - split.
    + constructor. apply PHFPAxiomI.
    + intros [[Hpq Hpqf] [Hqr Hqrf]]. split.
      * exact (@phf_provable_imp_trans Atom H p q r Hpq Hqr).
      * intro Hp. apply Hqrf, Hpqf, Hp.
  - split.
    + constructor. apply PHFPIdentity.
    + exact (fun Hp => Hp).
  - split.
    + constructor. apply PHFPEfq.
    + contradiction.
  - eapply p_aczel_slash_modus_ponens.
    + now apply IHd1.
    + now apply IHd2.
  - split.
    + constructor. now apply PHFPAFortiori.
    + intro Hignored. now apply IHd.
  - split; [now apply IHd1 | now apply IHd2].
Qed.

Theorem phf_aczel_slash_iff_provable :
  forall (Atom : Type) (H : phf_hilbert Atom),
    (forall p, phf_schema H p ->
      p_aczel_slash (phf_provable H) p) ->
    forall p,
      p_aczel_slash (phf_provable H) p <-> phf_provable H p.
Proof.
  intros Atom H Hschema p; split.
  - apply phf_provable_of_aczel_slash.
  - intros [d]. now apply phf_aczel_slash_of_proof.
Qed.

Theorem phf_disjunctive_of_schema_aczel_slash :
  forall (Atom : Type) (H : phf_hilbert Atom),
    (forall p, phf_schema H p ->
      p_aczel_slash (phf_provable H) p) ->
    pformula_predicate_disjunctive (phf_provable H).
Proof.
  intros Atom H Hschema.
  apply pformula_disjunctive_of_aczel_slash_iff.
  now apply phf_aczel_slash_iff_provable.
Qed.

Lemma phf_aczel_slash_axiom_ser :
  forall (Atom : Type) (H : phf_hilbert Atom),
    phf_provable H (@pk2_axiom_ser Atom) ->
    p_aczel_slash (phf_provable H) (@pk2_axiom_ser Atom).
Proof.
  intros Atom H Hser.
  apply (proj2 (@p_aczel_slash_neg Atom (phf_provable H) (pneg ptop))).
  split; [exact Hser |]. intro HnegTop.
  apply (proj1 (@p_aczel_slash_neg Atom (phf_provable H) ptop) HnegTop).
  apply (proj2 (@p_aczel_slash_top Atom (phf_provable H))).
  constructor. apply PHFPIdentity.
Qed.

Lemma phf_aczel_slash_axiom_rfl :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_provable H (pk2_axiom_rfl p q) ->
    p_aczel_slash (phf_provable H) (pk2_axiom_rfl p q).
Proof.
  intros Atom H p q Hrfl.
  apply (proj2 (@p_aczel_slash_imp Atom (phf_provable H)
    (PAnd p (PImp p q)) q)).
  split; [exact Hrfl |].
  intros [Hp [_ Hpq]]. now apply Hpq.
Qed.

Lemma phf_aczel_slash_axiom_tra1 :
  forall (Atom : Type) (H : phf_hilbert Atom) p q r,
    phf_provable H (pk2_axiom_tra1 p q r) ->
    p_aczel_slash (phf_provable H) (pk2_axiom_tra1 p q r).
Proof.
  intros Atom H p q r Htra.
  apply (proj2 (@p_aczel_slash_imp Atom (phf_provable H)
    (PImp p q) (PImp r (PImp p q)))). split; [exact Htra |].
  intros Hpq. apply (proj2 (@p_aczel_slash_imp Atom (phf_provable H)
    r (PImp p q))). split.
  - apply phf_provable_mdp with (p := PImp p q); [exact Htra |].
    exact (proj1 (proj1 (@p_aczel_slash_imp Atom (phf_provable H)
      p q) Hpq)).
  - intros _. exact Hpq.
Qed.

Theorem phf_F_disjunctive :
  forall Atom : Type,
    pformula_predicate_disjunctive
      (phf_provable (phf_hilbert_F Atom)).
Proof.
  intro Atom. apply phf_disjunctive_of_schema_aczel_slash.
  intros p H; contradiction.
Qed.

Theorem phf_F_Ser_disjunctive :
  forall Atom : Type,
    pformula_predicate_disjunctive
      (phf_provable (phf_hilbert_F_Ser Atom)).
Proof.
  intro Atom. apply phf_disjunctive_of_schema_aczel_slash.
  intros p ->. apply phf_aczel_slash_axiom_ser,
    phf_provable_of_schema. reflexivity.
Qed.

Theorem phf_F_Rfl_disjunctive :
  forall Atom : Type,
    pformula_predicate_disjunctive
      (phf_provable (phf_hilbert_F_Rfl Atom)).
Proof.
  intro Atom. apply phf_disjunctive_of_schema_aczel_slash.
  intros s [p [q ->]]. apply phf_aczel_slash_axiom_rfl,
    phf_provable_of_schema. now exists p, q.
Qed.

Theorem phf_F_Tra1_disjunctive :
  forall Atom : Type,
    pformula_predicate_disjunctive
      (phf_provable (phf_hilbert_F_Tra1 Atom)).
Proof.
  intro Atom. apply phf_disjunctive_of_schema_aczel_slash.
  intros s [p [q [r ->]]]. apply phf_aczel_slash_axiom_tra1,
    phf_provable_of_schema. now exists p, q, r.
Qed.

(** * Weak deduction and finite support *)

Inductive phf_deduction {Atom : Type} (H : phf_hilbert Atom)
    (Gamma : pformula Atom -> Prop) : pformula Atom -> Prop :=
| PHFDCtx : forall p, Gamma p -> phf_deduction H Gamma p
| PHFDTheorem : forall p, phf_provable H p -> phf_deduction H Gamma p
| PHFDModusPonens : forall p q,
    phf_provable H (PImp p q) ->
    phf_deduction H Gamma p -> phf_deduction H Gamma q
| PHFDAndRule : forall p q,
    phf_deduction H Gamma p -> phf_deduction H Gamma q ->
    phf_deduction H Gamma (PAnd p q).

Arguments PHFDCtx {Atom H Gamma p} _.
Arguments PHFDTheorem {Atom H Gamma p} _.
Arguments PHFDModusPonens {Atom H Gamma p q} _ _.
Arguments PHFDAndRule {Atom H Gamma p q} _ _.

Lemma phf_deducible_of_provable :
  forall (Atom : Type) (H : phf_hilbert Atom) Gamma p,
    phf_provable H p -> phf_deduction H Gamma p.
Proof. intros; now apply PHFDTheorem. Qed.

Lemma phf_deduction_empty_iff :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    phf_deduction H (fun _ => False) p <-> phf_provable H p.
Proof.
  intros Atom H p; split.
  - intro d; induction d.
    + contradiction.
    + assumption.
    + now apply phf_provable_mdp with (p := p).
    + now apply phf_provable_and_rule.
  - now apply PHFDTheorem.
Qed.

Lemma phf_deduction_weaken :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (Gamma Delta : pformula Atom -> Prop),
    (forall p, Gamma p -> Delta p) -> forall p,
    phf_deduction H Gamma p -> phf_deduction H Delta p.
Proof.
  intros Atom H Gamma Delta Hsub p d; induction d.
  - apply PHFDCtx, Hsub; assumption.
  - now apply PHFDTheorem.
  - eapply PHFDModusPonens; eassumption.
  - now apply PHFDAndRule.
Qed.

Theorem phf_weak_deduction_iff :
  forall (Atom : Type) (H : phf_hilbert Atom) p q,
    phf_deduction H (fun r => r = p) q <->
    phf_provable H (PImp p q).
Proof.
  intros Atom H p q; split.
  - intro d; induction d.
    + subst p0. constructor. apply PHFPIdentity.
    + now apply phf_provable_afortiori.
    + eapply phf_provable_imp_trans; eauto.
    + now apply phf_provable_imp_and.
  - intro Hpq. eapply PHFDModusPonens; [exact Hpq |].
    apply PHFDCtx. reflexivity.
Qed.

Theorem phf_deduction_finite_list_support :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (Gamma : pformula Atom -> Prop) p,
    phf_deduction H Gamma p <->
    exists delta : list (pformula Atom),
      (forall q, In q delta -> Gamma q) /\
      phf_deduction H (fun q => In q delta) p.
Proof.
  intros Atom H Gamma p; split.
  - intro d; induction d.
    + exists [p]; split; [intros q [<- | []]; assumption |].
      apply PHFDCtx. now left.
    + exists []; split; [intros q [] | now apply PHFDTheorem].
    + destruct IHd as [delta [Hdelta Hd]]. exists delta; split; [exact Hdelta |].
      eapply PHFDModusPonens; eassumption.
    + destruct IHd1 as [delta [Hdelta Hd]].
      destruct IHd2 as [epsilon [Hepsilon He]].
      exists (delta ++ epsilon); split.
      * intros r Hr. apply in_app_or in Hr. destruct Hr; auto.
      * apply PHFDAndRule.
        -- eapply phf_deduction_weaken; [|exact Hd].
           intros r Hr. apply in_or_app; now left.
        -- eapply phf_deduction_weaken; [|exact He].
           intros r Hr. apply in_or_app; now right.
  - intros [delta [Hsub Hd]].
    eapply phf_deduction_weaken; [exact Hsub | exact Hd].
Qed.
