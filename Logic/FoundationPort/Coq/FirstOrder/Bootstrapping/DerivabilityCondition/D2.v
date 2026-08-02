(** Standard-natural Hilbert--Bernays D2 for executable proof codes. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import GenericEntailment GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic Coding.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import D1.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Modus ponens for arbitrary typed propositions *)

(** The proof-relevant alternative calculus itself is a one-sided classical
    calculus.  Packaging this once lets the generic cut construction derive
    modus ponens without a bespoke proof tree. *)
Definition boot_derivation2_one_sided_lk (L : language) (T : theory L) :
    generic_one_sided_lk (semiformula_connectives L nat 0)
      (first_order_derivation2 L T).
Proof.
  constructor.
  - intro p. apply (FOD2Closed p); [now left | now right; left].
  - intros Delta Gamma d Hsub. exact (FOD2Weakening d Hsub).
  - apply FOD2Verum. now left.
  - intros p q Gamma dp dq.
    apply (FOD2And (p := p) (q := q)); [now left | |].
    + apply (FOD2Weakening dp).
      intros x [Hx | Hx]; [now left | right; right; exact Hx].
    + apply (FOD2Weakening dq).
      intros x [Hx | Hx]; [now left | right; right; exact Hx].
  - intros p q Gamma d.
    apply (FOD2Or (p := p) (q := q)); [now left |].
    apply (FOD2Weakening d).
    intros x [Hx | [Hx | Hx]].
    + now left.
    + right. now left.
    + right. right. right. exact Hx.
Defined.

Definition boot_derivation2_one_sided_lk_cut
    (L : language) (T : theory L) :
    generic_one_sided_lk_cut (semiformula_connectives L nat 0)
      (first_order_derivation2 L T).
Proof.
  constructor.
  - exact (@boot_derivation2_one_sided_lk L T).
  - intros p Gamma Delta dp dn.
    apply (FOD2Cut (p := p)).
    + apply (FOD2Weakening dp).
      exact (@generic_list_subset_cons_append_right
        (proposition L) p Gamma Delta).
    + apply (FOD2Weakening dn).
      exact (@generic_list_subset_cons_append_left
        (proposition L) (semiformula_neg p) Gamma Delta).
Defined.

Definition boot_derivation2_entailment (L : language) (T : theory L) :
    generic_entailment unit (proposition L) :=
  {| generic_proof := fun _ p => first_order_derivation2 L T [p] |}.

Definition boot_derivation2_principal (L : language) (T : theory L) :
    generic_principal_entailment
      (@boot_derivation2_entailment L T)
      (first_order_derivation2 L T) tt.
Proof.
  constructor. intro p.
  refine {| generic_equiv_to := fun d => d;
            generic_equiv_from := fun d => d |}; reflexivity.
Defined.

Definition boot_derivation2_modus_ponens (L : language) (T : theory L) :
    generic_modus_ponens
      (@boot_derivation2_entailment L T)
      (semiformula_connectives L nat 0) tt :=
  @generic_principal_modus_ponens unit (proposition L)
    (@boot_derivation2_entailment L T)
    (semiformula_connectives L nat 0)
    (first_order_derivation2 L T) tt
    (@boot_derivation2_principal L T)
    (@semiformula_neg_involutive L nat 0)
    (fun _ _ => eq_refl)
    (fun _ _ => eq_refl)
    (@boot_derivation2_one_sided_lk_cut L T).

Theorem boot_derivation2_modus_ponens_raw : forall L T
    (p q : proposition L),
  first_order_derivation2 L T [semiformula_imp p q] ->
  first_order_derivation2 L T [p] ->
  first_order_derivation2 L T [q].
Proof.
  intros L T p q Himp Hp.
  exact (generic_modus_ponens_raw (@boot_derivation2_modus_ponens L T)
    p q Himp Hp).
Qed.

Theorem boot_formula_provability_modus_ponens : forall L T EL ET
    (p q : proposition L),
  @boot_provable L EL T ET
      (boot_typed_formula_quote EL (semiformula_imp p q)) ->
  @boot_provable L EL T ET (boot_typed_formula_quote EL p) ->
  @boot_provable L EL T ET (boot_typed_formula_quote EL q).
Proof.
  intros L T EL ET p q Himp Hp.
  apply (proj2 (@boot_provable_quote_iff L EL T ET q)).
  apply (proj1 (@boot_provable_quote_iff L EL T ET
    (semiformula_imp p q))) in Himp.
  apply (proj1 (@boot_provable_quote_iff L EL T ET p)) in Hp.
  destruct Himp as [dimp]. destruct Hp as [dp]. constructor.
  exact (@boot_derivation2_modus_ponens_raw L T p q dimp dp).
Qed.

(** Raw provability of quoted sentences is closed under modus ponens.  The
    proof is factored through the already checked classical theory entailment,
    rather than manipulating proof-code constructors by hand. *)
Theorem boot_provability_modus_ponens : forall L T EL ET
    (sigma tau : sentence L),
  @boot_sentence_provable L EL T ET (semiformula_imp sigma tau) ->
  @boot_sentence_provable L EL T ET sigma ->
  @boot_sentence_provable L EL T ET tau.
Proof.
  intros L T EL ET sigma tau Himp Hsigma.
  apply (proj2 (@boot_sentence_provable_iff_theory L T EL ET tau)).
  apply (proj1 (@boot_sentence_provable_iff_theory L T EL ET
    (semiformula_imp sigma tau))) in Himp.
  apply (proj1 (@boot_sentence_provable_iff_theory L T EL ET sigma))
    in Hsigma.
  destruct Himp as [dimp]. destruct Hsigma as [dsigma]. constructor.
  exact (generic_modus_ponens_raw
    (generic_classical_mdp (first_order_theory_classical T))
    sigma tau dimp dsigma).
Qed.

(** A theorem-level D2 implication, convenient when raw provability is used
    as the theorem predicate of an abstract provability development. *)
Corollary boot_provability_D2 : forall L T EL ET
    (sigma tau : sentence L),
  @boot_sentence_provable L EL T ET (semiformula_imp sigma tau) ->
  (@boot_sentence_provable L EL T ET sigma ->
   @boot_sentence_provable L EL T ET tau).
Proof.
  intros L T EL ET sigma tau Himp Hsigma.
  exact (@boot_provability_modus_ponens L T EL ET sigma tau Himp Hsigma).
Qed.
