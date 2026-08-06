(**
  Finite-context derivability-condition adapters.

  The concrete Lean [StandardProvability] development builds its proof
  predicate from Delta-one coding and then lifts the D2/D3 theorems into an
  arbitrary finite context.  The coding layer is intentionally outside this
  port, but the context lifting is pure first-order LK.  The lemmas below
  isolate that reusable core: a singleton theorem is weakened into the
  context, and the already available cut rule performs modus ponens twice.

  [boot_context_provable] uses the same one-sided finite-context convention
  as [first_order_derivation2]: a context [Gamma] contributes the negated
  formulas [map semiformula_neg Gamma] to the sequent.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import D1 D2 D3.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** At the standard natural numbers, raw proof-code provability is an
    external proposition.  This record packages exactly the theorem-level
    interface used by the source's [Theory.standardProvability] object,
    without claiming that its internal Delta-one predicate has been
    reconstructed. *)
Record boot_standard_provability (L : language) (T : theory L)
    (EL : language_encodable L) (ET : boot_theory_encoding EL T) : Type := {
  boot_standard_prov : sentence L -> Prop;
  boot_standard_D1 : forall sigma,
    first_order_theory_provable T sigma -> boot_standard_prov sigma;
  boot_standard_sound : forall sigma,
    boot_standard_prov sigma -> first_order_theory_provable T sigma;
  boot_standard_modus_ponens : forall sigma tau,
    boot_standard_prov (semiformula_imp sigma tau) ->
    boot_standard_prov sigma -> boot_standard_prov tau
}.

Arguments boot_standard_prov {L T EL ET} _ _.
Arguments boot_standard_D1 {L T EL ET} _ _ _.
Arguments boot_standard_sound {L T EL ET} _ _ _.
Arguments boot_standard_modus_ponens {L T EL ET} _ _ _ _ _.

(** The checked executable proof predicate realizes the bundled interface. *)
Definition boot_standard_provability_of_code : forall L T EL ET,
    @boot_standard_provability L T EL ET.
Proof.
  intros L T EL ET.
  refine {| boot_standard_prov := @boot_sentence_provable L EL T ET;
            boot_standard_D1 := fun sigma =>
              @boot_internalize_provability L T EL ET sigma;
            boot_standard_sound := fun sigma =>
              @boot_sentence_provable_sound L T EL ET sigma;
            boot_standard_modus_ponens := fun sigma tau =>
              @boot_provability_modus_ponens L T EL ET sigma tau |}.
Defined.

Lemma boot_standard_provability_of_code_iff_theory : forall L T EL ET
    (sigma : sentence L),
  boot_standard_prov (@boot_standard_provability_of_code L T EL ET) sigma <->
  first_order_theory_provable T sigma.
Proof.
  intros L T EL ET sigma.
  exact (@boot_sentence_provable_iff_theory L T EL ET sigma).
Qed.

(** A finite-context proof of a proposition in the ambient theory. *)
Definition boot_context_proof {L : language} (T : theory L)
    (Gamma : list (proposition L)) (p : proposition L) : Type :=
  first_order_derivation2 L T
    (p :: map (@semiformula_neg L nat 0) Gamma).

Definition boot_context_provable {L : language} (T : theory L)
    (Gamma : list (proposition L)) (p : proposition L) : Prop :=
  inhabited (boot_context_proof T Gamma p).

(** Any singleton derivation is available in every finite context. *)
Lemma boot_context_weaken : forall (L : language) (T : theory L)
  (Gamma : list (proposition L)) (p : proposition L),
  first_order_derivation2 L T [p] ->
  boot_context_proof T Gamma p.
Proof.
  intros L T Gamma p d.
  unfold boot_context_proof.
  apply (FOD2Weakening d).
  intros q [Hq | Hq].
  - now left.
  - contradiction.
Qed.

(** Raw finite-context modus ponens.  The two assumptions may use the same
    context; duplicate occurrences are removed by the final weakening. *)
Theorem boot_context_modus_ponens_raw : forall (L : language) (T : theory L)
  (Gamma : list (proposition L)) (p q : proposition L),
  boot_context_proof T Gamma (semiformula_imp p q) ->
  boot_context_proof T Gamma p ->
  boot_context_proof T Gamma q.
Proof.
  intros L T Gamma p q dimp dp.
  unfold boot_context_proof in *.
  set (N := map (@semiformula_neg L nat 0) Gamma).
  change (first_order_derivation2 L T
      (semiformula_imp p q :: N)) in dimp.
  change (first_order_derivation2 L T (p :: N)) in dp.
  pose (K := @boot_derivation2_one_sided_lk_cut L T).
  pose proof (generic_lk_tensor (generic_lk_cut_base K)
      (generic_lk_identity (generic_lk_cut_base K) p)
      (generic_lk_identity (generic_lk_cut_base K)
        (semiformula_neg q))) as dcontra.
  assert (econtra :
      Semiformula_and p (semiformula_neg q) ::
        [semiformula_neg p;
         semiformula_neg (semiformula_neg q)] =
      [semiformula_neg (semiformula_imp p q);
       semiformula_neg p; q]).
  { simpl. rewrite (@semiformula_neg_involutive L nat 0 q).
    rewrite (@semiformula_neg_involutive L nat 0 p).
    reflexivity. }
  pose proof (@generic_lk_cast (proposition L)
      (first_order_derivation2 L T) _ _ dcontra econtra) as dcontra'.
  pose proof (generic_lk_cut_raw K (semiformula_imp p q) N
      [semiformula_neg p; q] dimp dcontra') as d1.
  assert (Hreorder1 :
      generic_list_subset (N ++ [semiformula_neg p; q])
        (semiformula_neg p :: q :: N)).
  { intros r Hr.
    apply (proj1 (@generic_list_member_app_iff
      (proposition L) r N [semiformula_neg p; q])) in Hr.
    destruct Hr as [Hr | [Hr | Hr]].
    - right. right. exact Hr.
    - now left.
    - destruct Hr as [Hr | Hr].
      + right; left; exact Hr.
      + contradiction.
  }
  pose proof (generic_lk_contra (generic_lk_cut_base K) d1 Hreorder1)
    as d1'.
  pose proof (generic_lk_cut_raw K p N
      (q :: N) dp d1') as d2.
  assert (Hreorder2 :
      generic_list_subset (N ++ q :: N) (q :: N)).
  { intros r Hr.
    apply (proj1 (@generic_list_member_app_iff
      (proposition L) r N (q :: N))) in Hr.
    destruct Hr as [Hr | [Hr | Hr]].
    - right. exact Hr.
    - simpl in Hr. now left.
    - right. exact Hr.
  }
  exact (generic_lk_contra (generic_lk_cut_base K) d2 Hreorder2).
Qed.

Corollary boot_context_modus_ponens : forall (L : language) (T : theory L)
  (Gamma : list (proposition L)) (p q : proposition L),
  boot_context_provable T Gamma (semiformula_imp p q) ->
  boot_context_provable T Gamma p ->
  boot_context_provable T Gamma q.
Proof.
  intros L T Gamma p q [dimp] [dp].
  constructor.
  exact (boot_context_modus_ponens_raw dimp dp).
Qed.

(** Contextual form of D2.  The premise [hD2] is the singleton theorem
    supplied by a concrete provability predicate. *)
Theorem boot_context_D2 : forall (L : language) (T : theory L)
    (Gamma : list (proposition L))
    (box : proposition L -> proposition L) p q,
  first_order_derivation2 L T
    [semiformula_imp (box (semiformula_imp p q))
      (semiformula_imp (box p) (box q))] ->
  boot_context_provable T Gamma (box (semiformula_imp p q)) ->
  boot_context_provable T Gamma (box p) ->
  boot_context_provable T Gamma (box q).
Proof.
  intros L T Gamma box p q hD2 hbpq hbp.
  assert (Hmid : boot_context_provable T Gamma
      (semiformula_imp (box p) (box q))).
  { apply (@boot_context_modus_ponens L T Gamma
      (box (semiformula_imp p q))
      (semiformula_imp (box p) (box q))).
    - constructor. apply boot_context_weaken. exact hD2.
    - exact hbpq. }
  exact (@boot_context_modus_ponens L T Gamma
    (box p) (box q) Hmid hbp).
Qed.

(** Contextual form of D3, derived from the same factored modus-ponens
    adapter rather than repeating a cut proof. *)
Theorem boot_context_D3 : forall (L : language) (T : theory L)
    (Gamma : list (proposition L))
    (box : proposition L -> proposition L) p,
  first_order_derivation2 L T
    [semiformula_imp (box p) (box (box p))] ->
  boot_context_provable T Gamma (box p) ->
  boot_context_provable T Gamma (box (box p)).
Proof.
  intros L T Gamma box p hD3 hbp.
  apply (@boot_context_modus_ponens L T Gamma
    (box p) (box (box p))).
  - constructor. apply boot_context_weaken. exact hD3.
  - exact hbp.
Qed.
