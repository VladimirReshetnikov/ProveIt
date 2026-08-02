(**
  Typed quotation of proof-relevant LK derivations.

  Each [first_order_derivation2] constructor is translated to the matching raw
  bootstrapped node.  The main theorem simultaneously certifies that the code
  is accepted by [boot_derivation_code], so downstream provability arguments
  never need to trust an unverified serializer.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2 Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Typed Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint boot_derivation2_quote {L T Gamma}
    (EL : language_encodable L) (ET : boot_theory_encoding EL T)
    (d : first_order_derivation2 L T Gamma) : nat :=
  match d with
  | @FOD2Closed _ _ _ p _ _ =>
      boot_axL (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p)
  | @FOD2Axiom _ _ _ sigma _ _ =>
      boot_axiom_rule (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL (first_order_sentence_embed sigma))
  | @FOD2Verum _ _ _ _ => boot_verum_intro (boot_sequent_quote EL Gamma)
  | @FOD2And _ _ _ p q _ dp dq =>
      boot_and_intro (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p) (boot_typed_formula_quote EL q)
        (@boot_derivation2_quote L T _ EL ET dp)
        (@boot_derivation2_quote L T _ EL ET dq)
  | @FOD2Or _ _ _ p q _ dpq =>
      boot_or_intro (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p) (boot_typed_formula_quote EL q)
        (@boot_derivation2_quote L T _ EL ET dpq)
  | @FOD2All _ _ _ p _ dp =>
      boot_all_intro (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p)
        (@boot_derivation2_quote L T _ EL ET dp)
  | @FOD2Exists _ _ _ p _ t dp =>
      boot_exists_intro (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p) (boot_typed_quote EL t)
        (@boot_derivation2_quote L T _ EL ET dp)
  | @FOD2Weakening _ _ _ _ dp _ =>
      boot_weakening_rule (boot_sequent_quote EL Gamma)
        (@boot_derivation2_quote L T _ EL ET dp)
  | @FOD2Shift _ _ source dp =>
      boot_shift_rule (boot_sequent_quote EL (first_order_sequent_shift source))
        (@boot_derivation2_quote L T _ EL ET dp)
  | @FOD2Cut _ _ _ p dp dn =>
      boot_cut_rule (boot_sequent_quote EL Gamma)
        (boot_typed_formula_quote EL p)
        (@boot_derivation2_quote L T _ EL ET dp)
        (@boot_derivation2_quote L T _ EL ET dn)
  end.

Lemma boot_derivation2_quote_conseq : forall L T Gamma EL ET
    (d : first_order_derivation2 L T Gamma),
  boot_proof_conseq (@boot_derivation2_quote L T Gamma EL ET d) =
  boot_sequent_quote EL Gamma.
Proof.
  intros. destruct d; apply boot_proof_conseq_node.
Qed.

Theorem boot_derivation2_quote_recognized : forall L T Gamma EL ET
    (d : first_order_derivation2 L T Gamma),
  @boot_derivation_code L EL T ET
    (map (boot_typed_formula_quote EL) Gamma)
    (@boot_derivation2_quote L T Gamma EL ET d).
Proof.
  intros L T Gamma EL ET d. induction d.
  - apply Boot_derivation_axL.
    + apply boot_is_formula_set_quote.
    + apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + rewrite <- boot_typed_formula_quote_neg.
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
  - apply Boot_derivation_axiom.
    + apply boot_is_formula_set_quote.
    + apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + apply boot_theory_classifier_formula_spec.
      exists sigma. now split.
  - apply Boot_derivation_verum.
    + apply boot_is_formula_set_quote.
    + change (In (boot_typed_formula_quote EL (Semiformula_verum 0))
        (map (boot_typed_formula_quote EL) Gamma)).
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
  - apply Boot_derivation_and.
    + apply boot_is_formula_set_quote.
    + change (In (boot_typed_formula_quote EL (Semiformula_and p q))
        (map (boot_typed_formula_quote EL) Gamma)).
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + exact IHd1.
    + exact IHd2.
  - apply Boot_derivation_or.
    + apply boot_is_formula_set_quote.
    + change (In (boot_typed_formula_quote EL (Semiformula_or p q))
        (map (boot_typed_formula_quote EL) Gamma)).
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + exact IHd.
  - apply Boot_derivation_all.
    + apply boot_is_formula_set_quote.
    + change (In (boot_typed_formula_quote EL (Semiformula_all p))
        (map (boot_typed_formula_quote EL) Gamma)).
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + apply boot_typed_formula_quote_recognized.
    + simpl in IHd.
      rewrite boot_formula_free_code_quote, <- boot_sequent_shift_quote.
      exact IHd.
  - apply Boot_derivation_exists.
    + apply boot_is_formula_set_quote.
    + change (In (boot_typed_formula_quote EL (Semiformula_exists p))
        (map (boot_typed_formula_quote EL) Gamma)).
      apply boot_sequent_quote_member_iff.
      now apply boot_list_in_of_generic_list_member.
    + apply boot_typed_formula_quote_recognized.
    + apply boot_typed_quote_recognized.
    + simpl in IHd.
      rewrite boot_typed_quote_decode.
      change (@boot_derivation_code L EL T ET
        (boot_formula_subst_code EL (fun _ : Fin.t 1 => t)
          (semiformula_code EL boot_nat_encoding p) ::
          map (boot_typed_formula_quote EL) Gamma)
        (@boot_derivation2_quote L T
          (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)
          EL ET d)).
      rewrite boot_formula_subst_code_quote.
      exact IHd.
  - apply Boot_derivation_weakening with
      (Delta := map (boot_typed_formula_quote EL) Delta).
    + apply boot_is_formula_set_quote.
    + intros code Hcode.
      apply in_map_iff in Hcode. destruct Hcode as [p [<- Hp]].
      apply in_map. apply boot_list_in_of_generic_list_member.
      apply g. now apply generic_list_member_of_list_in.
    + exact IHd.
  - cbn [boot_derivation2_quote].
    rewrite boot_sequent_shift_quote.
    unfold boot_sequent_quote.
    rewrite boot_sequent_shift_quote.
    apply Boot_derivation_shift.
    + rewrite <- boot_sequent_shift_quote.
      apply boot_is_formula_set_quote.
    + exact IHd.
  - apply Boot_derivation_cut.
    + apply boot_is_formula_set_quote.
    + apply boot_typed_formula_quote_recognized.
    + exact IHd1.
    + rewrite <- boot_typed_formula_quote_neg. exact IHd2.
Qed.

Corollary boot_derivation2_quote_derivation : forall L T Gamma EL ET
    (d : first_order_derivation2 L T Gamma),
  @boot_derivation L EL T ET
    (@boot_derivation2_quote L T Gamma EL ET d).
Proof.
  intros. exists (map (boot_typed_formula_quote EL) Gamma).
  apply boot_derivation2_quote_recognized.
Qed.

Corollary boot_derivation2_quote_proof : forall L T EL ET
    (p : proposition L) (d : first_order_derivation2 L T [p]),
  @boot_proof L EL T ET (@boot_derivation2_quote L T [p] EL ET d)
    (boot_typed_formula_quote EL p).
Proof.
  intros L T EL ET p d.
  pose proof (@boot_derivation2_quote_recognized
    L T [p] EL ET d) as H. simpl in H. exact H.
Qed.

Corollary boot_derivable2_quote_provable : forall L T EL ET
    (p : proposition L),
  first_order_derivable2 T [p] ->
  @boot_provable L EL T ET (boot_typed_formula_quote EL p).
Proof.
  intros L T EL ET p [d].
  exists (@boot_derivation2_quote L T [p] EL ET d).
  apply boot_derivation2_quote_proof.
Qed.
