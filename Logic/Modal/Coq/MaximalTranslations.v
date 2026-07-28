(**
  The two maximal one-world translations and their unprovability
  consequences.

  This module ports the theorem surfaces of the pinned Foundation files

    - [Modal/Maximal/Basic.lean], and
    - the remaining results of [Modal/Maximal/Unprovability.lean].

  Foundation converts the box-free results to a separate propositional
  syntax.  The present development deliberately shares the primitive
  atom/falsity/implication syntax between its modal and propositional views,
  so the two [toIP] counterparts below are representation-only aliases.
  Classical theoremhood is therefore expressed by [classical_tautology].
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke HilbertK NormalHilbert CanonicalK LogicInfrastructure
  Boxdot CanonicalTrivVer GLAlternativeSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The translations *)

Fixpoint triv_translate {AtomType} (p : formula AtomType)
    : formula AtomType :=
  match p with
  | Atom a => Atom a
  | Bottom => Bottom
  | Imp q r => Imp (triv_translate q) (triv_translate r)
  | Box q => triv_translate q
  end.

Fixpoint ver_translate {AtomType} (p : formula AtomType)
    : formula AtomType :=
  match p with
  | Atom a => Atom a
  | Bottom => Bottom
  | Imp q r => Imp (ver_translate q) (ver_translate r)
  | Box _ => Top
  end.

Lemma triv_translate_degree_zero :
  forall (AtomType : Type) (p : formula AtomType),
    modal_degree (triv_translate p) = 0.
Proof.
  intros AtomType p; induction p; simpl; auto.
  now rewrite IHp1, IHp2.
Qed.

Lemma ver_translate_degree_zero :
  forall (AtomType : Type) (p : formula AtomType),
    modal_degree (ver_translate p) = 0.
Proof.
  intros AtomType p; induction p; simpl; auto.
  now rewrite IHp1, IHp2.
Qed.

(** Coq's modal formula type already is the common atom/falsity/implication
    representation used for propositional formulae.  These definitions are
    the exact representation-level counterparts of Foundation's [toIP]
    lemmas; their equations are judgmental. *)
Definition triv_translate_toIP {AtomType} (p : formula AtomType)
    : formula AtomType := triv_translate p.

Definition ver_translate_toIP {AtomType} (p : formula AtomType)
    : formula AtomType := ver_translate p.

Lemma triv_translate_toIP_eq :
  forall (AtomType : Type) (p : formula AtomType),
    triv_translate_toIP p = triv_translate p.
Proof. reflexivity. Qed.

Lemma ver_translate_toIP_eq :
  forall (AtomType : Type) (p : formula AtomType),
    ver_translate_toIP p = ver_translate p.
Proof. reflexivity. Qed.

(** * Pointwise semantic equations *)

Lemma triv_translate_truth_on_Triv_frame :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (w : World F) (p : formula AtomType),
    Triv_kripke_frame_class F ->
    (satisfies F V w p <-> satisfies F V w (triv_translate p)).
Proof.
  intros AtomType F V w p [Hrefl Hcore].
  revert w; induction p as [a | | p IHp q IHq | p IHp]; intro w; simpl.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - split.
    + intro Hbox. apply (proj1 (IHp w)), Hbox, Hrefl.
    + intros Hlocal y Rwy. apply (proj2 (IHp y)).
      apply Hcore in Rwy. now subst y.
Qed.

Lemma ver_translate_truth_on_Ver_frame :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (w : World F) (p : formula AtomType),
    Ver_kripke_frame_class F ->
    (satisfies F V w p <-> satisfies F V w (ver_translate p)).
Proof.
  intros AtomType F V w p Hisolated.
  revert w; induction p as [a | | p IHp q IHq | p IHp]; intro w; simpl.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - split.
    + intros _. tauto.
    + intros _ y Rwy. exfalso. exact (Hisolated w y Rwy).
Qed.

(** Evaluation of a translated formula only consults the values assigned to
    atoms.  The arbitrary values that [classical_eval] permits for boxed
    formulae are irrelevant because both translations have degree zero. *)
Lemma classical_eval_triv_translate_satisfies :
  forall (AtomType : Type) (rho : formula AtomType -> Prop)
         (F : frame) (V : valuation AtomType F) (w : World F)
         (p : formula AtomType),
    (forall a, rho (Atom a) <-> V a w) ->
    (classical_eval rho (triv_translate p) <->
     satisfies F V w (triv_translate p)).
Proof.
  intros AtomType rho F V w p Hatoms.
  induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - apply Hatoms.
  - reflexivity.
  - now rewrite IHp, IHq.
  - exact IHp.
Qed.

Lemma classical_eval_ver_translate_satisfies :
  forall (AtomType : Type) (rho : formula AtomType -> Prop)
         (F : frame) (V : valuation AtomType F) (w : World F)
         (p : formula AtomType),
    (forall a, rho (Atom a) <-> V a w) ->
    (classical_eval rho (ver_translate p) <->
     satisfies F V w (ver_translate p)).
Proof.
  intros AtomType rho F V w p Hatoms.
  induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - apply Hatoms.
  - reflexivity.
  - now rewrite IHp, IHq.
  - reflexivity.
Qed.

(** * Lifting the classical core *)

Theorem normal_proves_of_classical_tautology :
  forall (Ax : modal_axiom_schema) (p : formula nat),
    classical_tautology p -> normal_proves Ax p.
Proof.
  intros Ax p Htaut.
  apply K_proves_normal, K_complete, classical_tautology_valid.
  exact Htaut.
Qed.

(** * Exact characterizations of Triv and Ver *)

Theorem Triv_proves_iff_triv_translate :
  forall p : formula nat,
    Triv_proves (Iff p (triv_translate p)).
Proof.
  intro p; induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - apply normal_proves_iff_refl.
  - apply normal_proves_iff_refl.
  - now apply normal_proves_imp_iff.
  - apply normal_proves_iff_intro.
    + eapply normal_proves_imp_trans_poly.
      * apply Np_extra. left. now exists p.
      * exact (normal_proves_iff_left IHp).
    + eapply normal_proves_imp_trans_poly.
      * exact (normal_proves_iff_right IHp).
      * apply Np_extra. right. now exists p.
Qed.

Theorem Ver_proves_iff_ver_translate :
  forall p : formula nat,
    Ver_proves (Iff p (ver_translate p)).
Proof.
  intro p; induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - apply normal_proves_iff_refl.
  - apply normal_proves_iff_refl.
  - now apply normal_proves_imp_iff.
  - apply normal_proves_iff_intro.
    + eapply Np_mp.
      * exact (Np_imply_K (@Top nat) (Box p)).
      * apply K_proves_normal. unfold Top, Neg.
        apply K_proves_identity.
    + eapply Np_mp.
      * exact (Np_imply_K (Box p) (@Top nat)).
      * apply Np_extra. now exists p.
Qed.

Lemma Triv_proves_triv_translate_classical_tautology :
  forall p : formula nat,
    Triv_proves p -> classical_tautology (triv_translate p).
Proof.
  intros p Hp; induction Hp; unfold classical_tautology in *; intro rho;
    simpl in *.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [[q ->] | [q ->]]; simpl; tauto.
  - exact (IHHp1 rho (IHHp2 rho)).
  - exact (IHHp rho).
Qed.

Lemma Ver_proves_ver_translate_classical_tautology :
  forall p : formula nat,
    Ver_proves p -> classical_tautology (ver_translate p).
Proof.
  intros p Hp; induction Hp; unfold classical_tautology in *; intro rho;
    simpl in *.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [q ->]; simpl; tauto.
  - exact (IHHp1 rho (IHHp2 rho)).
  - tauto.
Qed.

Theorem Triv_proves_iff_classical_tautology :
  forall p : formula nat,
    Triv_proves p <-> classical_tautology (triv_translate p).
Proof.
  intro p; split.
  - apply Triv_proves_triv_translate_classical_tautology.
  - intro Htaut.
    eapply Np_mp.
    + apply normal_proves_iff_right.
      exact (Triv_proves_iff_triv_translate p).
    + now apply normal_proves_of_classical_tautology.
Qed.

Theorem Ver_proves_iff_classical_tautology :
  forall p : formula nat,
    Ver_proves p <-> classical_tautology (ver_translate p).
Proof.
  intro p; split.
  - apply Ver_proves_ver_translate_classical_tautology.
  - intro Htaut.
    eapply Np_mp.
    + apply normal_proves_iff_right.
      exact (Ver_proves_iff_ver_translate p).
    + now apply normal_proves_of_classical_tautology.
Qed.

(** Source-facing aliases for Foundation's tautology theorem names. *)
Definition Triv_proves_iff_tautology :=
  Triv_proves_iff_classical_tautology.

Definition Ver_proves_iff_tautology :=
  Ver_proves_iff_classical_tautology.

Definition Triv_iff_trivTranslated := Triv_proves_iff_triv_translate.
Definition Triv_iff_provable_Cl := Triv_proves_iff_classical_tautology.
Definition Triv_iff_tautology := Triv_proves_iff_classical_tautology.

Definition Ver_iff_verTranslated := Ver_proves_iff_ver_translate.
Definition Ver_iff_provable_Cl := Ver_proves_iff_classical_tautology.
Definition Ver_iff_tautology := Ver_proves_iff_classical_tautology.

(** * The remaining maximal-unprovability results *)

Theorem Triv_unprovable_atomic_L :
  forall a : nat, ~ Triv_proves (L (Atom a)).
Proof.
  intros a Hproof.
  apply (Triv_proves_triv_translate_classical_tautology
    (p := L (Atom a)) Hproof (fun _ => False)).
  unfold L, Loeb; simpl. tauto.
Qed.

Theorem Ver_unprovable_P :
  ~ Ver_proves (@P nat).
Proof.
  intro Hproof.
  apply (Ver_proves_ver_translate_classical_tautology
    (p := @P nat) Hproof (fun _ => False)).
  unfold P, Neg, Top; simpl. tauto.
Qed.

Theorem K4_proves_triv_translate_classical_tautology :
  forall p : formula nat,
    K4_proves p -> classical_tautology (triv_translate p).
Proof.
  intros p Hp; induction Hp; unfold classical_tautology in *; intro rho;
    simpl in *.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [q ->]; simpl; tauto.
  - exact (IHHp1 rho (IHHp2 rho)).
  - exact (IHHp rho).
Qed.

Theorem GL_proves_ver_translate_classical_tautology :
  forall p : formula nat,
    GL_proves p -> classical_tautology (ver_translate p).
Proof.
  intros p Hp; induction Hp; unfold classical_tautology in *; intro rho;
    simpl in *.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [q ->]; simpl; tauto.
  - exact (IHHp1 rho (IHHp2 rho)).
  - tauto.
Qed.

(** The earlier GL/K4 modules use atom [0] as the separating witness.  The
    source theorems quantify over the atom, so expose that stronger surface
    here; the translated-tautology invariants make the generalization
    immediate. *)
Theorem K4_unprovable_AxiomL :
  forall a : nat, ~ K4_proves (L (Atom a)).
Proof.
  intros a Hproof.
  apply (K4_proves_triv_translate_classical_tautology
    (p := L (Atom a)) Hproof (fun _ => False)).
  unfold L, Loeb; simpl. tauto.
Qed.

Theorem GL_unprovable_AxiomT :
  forall a : nat, ~ GL_proves (T (Atom a)).
Proof.
  intros a Hproof.
  apply (GL_proves_ver_translate_classical_tautology
    (p := T (Atom a)) Hproof (fun _ => False)).
  unfold T, Top, Neg; simpl. tauto.
Qed.

(** Names mirroring the two source namespaces. *)
Definition Triv_unprovable_AxiomL := Triv_unprovable_atomic_L.
Definition Ver_unprovable_AxiomP := Ver_unprovable_P.

Definition K4_provable_trivTranslated_Cl :=
  K4_proves_triv_translate_classical_tautology.

Definition GL_provable_verTranslated_Cl :=
  GL_proves_ver_translate_classical_tautology.
