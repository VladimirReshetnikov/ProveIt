(**
  Decoding and range theorems for bootstrapped sequents and proofs.

  This module begins the converse direction to [Proof.Typed].  It first
  isolates the representation-independent fact needed by every rule case:
  a raw formula-set context is exactly a pointwise quotation of some typed
  sequent.  An executable option decoder realizes the witness.
*)

From Stdlib Require Import Lists.List.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic Typed.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Theorem boot_is_formula_set_has_quote : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma ->
  exists Delta : first_order_sequent L,
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros L EL Gamma H. induction H as [|code Gamma Hcode Hset IH].
  - exists []. reflexivity.
  - destruct (boot_is_semiformula_has_quote Hcode) as [p Hp].
    destruct IH as [Delta HDelta].
    exists (p :: Delta). simpl. unfold boot_typed_formula_quote at 1.
    now rewrite Hp, HDelta.
Qed.

Theorem boot_is_formula_set_quote_iff : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma <->
  exists Delta : first_order_sequent L,
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros; split.
  - apply boot_is_formula_set_has_quote.
  - intros [Delta <-]. apply boot_is_formula_set_quote.
Qed.

Lemma boot_formula_set_quote_unique : forall L EL
    (Gamma Delta : first_order_sequent L),
  map (boot_typed_formula_quote EL) Gamma =
  map (boot_typed_formula_quote EL) Delta -> Gamma = Delta.
Proof.
  intros L EL Gamma Delta H.
  apply boot_sequent_quote_injective with (EL := EL).
  unfold boot_sequent_quote. now rewrite H.
Qed.

Lemma boot_formula_set_quote_member : forall L EL
    (Delta : first_order_sequent L) code,
  In code (map (boot_typed_formula_quote EL) Delta) ->
  exists p : proposition L,
    In p Delta /\ boot_typed_formula_quote EL p = code.
Proof.
  intros L EL Delta code H.
  apply in_map_iff in H. destruct H as [p [Hcode Hp]].
  exists p. split; [assumption|now symmetry].
Qed.

Fixpoint boot_sequent_decode {L} (EL : language_encodable L)
    (Gamma : list nat) : option (first_order_sequent L) :=
  match Gamma with
  | [] => Some []
  | code :: rest =>
      match semiformula_decode EL boot_nat_encoding 0 code,
            boot_sequent_decode EL rest with
      | Some p, Some Delta => Some (p :: Delta)
      | _, _ => None
      end
  end.

Theorem boot_sequent_decode_quote : forall L EL
    (Delta : first_order_sequent L),
  boot_sequent_decode EL (map (boot_typed_formula_quote EL) Delta) =
  Some Delta.
Proof.
  intros L EL Delta. induction Delta as [|p Delta IH]; simpl.
  - reflexivity.
  - unfold boot_typed_formula_quote at 1.
    now rewrite semiformula_decode_code, IH.
Qed.

Theorem boot_sequent_decode_complete : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma ->
  exists Delta : first_order_sequent L,
    boot_sequent_decode EL Gamma = Some Delta /\
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros L EL Gamma H.
  destruct (boot_is_formula_set_has_quote H) as [Delta <-].
  exists Delta. split; [apply boot_sequent_decode_quote|reflexivity].
Qed.

Theorem boot_sequent_decode_some_iff : forall L EL Gamma Delta,
  @boot_is_formula_set L EL Gamma ->
  (@boot_sequent_decode L EL Gamma = Some Delta <->
   map (boot_typed_formula_quote EL) Delta = Gamma).
Proof.
  intros L EL Gamma Delta Hset.
  destruct (boot_is_formula_set_has_quote Hset) as [Theta HTheta].
  split.
  - intro Hdecode. rewrite <- HTheta in Hdecode.
    rewrite boot_sequent_decode_quote in Hdecode. injection Hdecode as ->.
    exact HTheta.
  - intro Hquote. rewrite <- Hquote. apply boot_sequent_decode_quote.
Qed.

(** Every recognized proof therefore has a uniquely decodable typed
    consequence sequent, independently of reconstruction of its rule tree. *)
Theorem boot_derivation_code_typed_consequence : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code ->
  exists Delta : first_order_sequent L,
    boot_sequent_decode EL Gamma = Some Delta /\
    boot_proof_conseq code = boot_sequent_quote EL Delta.
Proof.
  intros L EL T ET Gamma code H.
  destruct (boot_sequent_decode_complete
    (boot_derivation_code_formula_set H)) as [Delta [Hdecode Hquote]].
  exists Delta. split; [assumption|].
  rewrite (boot_derivation_code_conseq H).
  unfold boot_sequent_quote. now rewrite Hquote.
Qed.
