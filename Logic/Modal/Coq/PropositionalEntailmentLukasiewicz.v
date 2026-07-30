(** The generic implicational core of the classical Lukasiewicz basis.

    Foundation's [Propositional/Entailment/Cl/Łukasiewicz.lean] starts with
    modus ponens, K, S, and elimination of contraposition, then reconstructs
    classical reasoning.  The principal DNE, DNI, and explosion results below
    need no assumptions about conjunction, disjunction, truth, or formula
    equality, so their capability records only that exact boundary.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record generic_lukasiewicz_entailment {S F : Type}
    (E : generic_entailment S F)
    (C : generic_connectives F) (s : S) : Type := {
  generic_lukasiewicz_mdp : generic_modus_ponens E C s;
  generic_lukasiewicz_K : forall p q,
    generic_proof E s (generic_axiom_K C p q);
  generic_lukasiewicz_S : forall p q r,
    generic_proof E s (generic_axiom_S C p q r);
  generic_lukasiewicz_elim_contra : generic_has_axiom_elim_contra E C s
}.

Arguments generic_lukasiewicz_mdp {S F E C s} _.
Arguments generic_lukasiewicz_K {S F E C s} _ _ _.
Arguments generic_lukasiewicz_S {S F E C s} _ _ _ _.
Arguments generic_lukasiewicz_elim_contra {S F E C s} _.

Definition generic_lukasiewicz_identity_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) (p : F) :
    generic_proof E s (generic_imp C p p) :=
  generic_imp_identity_raw (generic_lukasiewicz_mdp H)
    (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) p.

Arguments generic_lukasiewicz_identity_raw {S F E C s} _ _.

(** Foundation's six-line derivation of DNE, expressed through the factored
    implicational combinators shared by every K/S Hilbert basis. *)
Definition generic_lukasiewicz_dne_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) (p : F) :
    generic_proof E s (generic_axiom_dne C p).
Proof.
  set (n := generic_neg C p).
  set (nn := generic_neg C n).
  set (nnn := generic_neg C nn).
  set (nnnn := generic_neg C nnn).
  pose (h1 := @generic_dhyp_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_K H)
    (generic_axiom_elim_contra C n nnn) nn
    (generic_elim_contra_raw (generic_lukasiewicz_elim_contra H) n nnn)).
  pose (h2 := generic_lukasiewicz_K H nn nnnn).
  pose (h3 := @generic_dhyp_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_K H)
    (generic_axiom_elim_contra C nn p) nn
    (generic_elim_contra_raw (generic_lukasiewicz_elim_contra H) nn p)).
  pose (h4 := @generic_under_apply_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_S H)
    nn (generic_imp C nnnn nn) (generic_imp C n nnn) h1 h2).
  pose (h5 := @generic_under_apply_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_S H)
    nn (generic_imp C n nnn) (generic_imp C nn p) h3 h4).
  exact (@generic_under_apply_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_S H)
    nn nn p h5 (generic_lukasiewicz_identity_raw H nn)).
Defined.

Arguments generic_lukasiewicz_dne_raw {S F E C s} _ _.

Definition generic_has_axiom_dne_of_lukasiewicz {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) :
    generic_has_axiom_dne E C s :=
  {| generic_dne_raw := generic_lukasiewicz_dne_raw H |}.

Definition generic_lukasiewicz_dni_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) (p : F) :
    generic_proof E s
      (generic_imp C p (generic_neg C (generic_neg C p))) :=
  generic_modus_ponens_raw (generic_lukasiewicz_mdp H)
    (generic_imp C
      (generic_neg C (generic_neg C (generic_neg C p)))
      (generic_neg C p))
    (generic_imp C p (generic_neg C (generic_neg C p)))
    (generic_elim_contra_raw (generic_lukasiewicz_elim_contra H)
      p (generic_neg C (generic_neg C p)))
    (generic_lukasiewicz_dne_raw H (generic_neg C p)).

Arguments generic_lukasiewicz_dni_raw {S F E C s} _ _.

(** Contradiction explodes directly through elimination of contraposition;
    bottom, truth, and their abbreviation laws are unnecessary. *)
Definition generic_lukasiewicz_explosion_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) (p q : F)
    (dp : generic_proof E s p)
    (dnp : generic_proof E s (generic_neg C p)) :
    generic_proof E s q :=
  generic_modus_ponens_raw (generic_lukasiewicz_mdp H) p q
    (generic_modus_ponens_raw (generic_lukasiewicz_mdp H)
      (generic_imp C (generic_neg C q) (generic_neg C p))
      (generic_imp C p q)
      (generic_elim_contra_raw (generic_lukasiewicz_elim_contra H) p q)
      (generic_modus_ponens_raw (generic_lukasiewicz_mdp H)
        (generic_neg C p)
        (generic_imp C (generic_neg C q) (generic_neg C p))
        (generic_lukasiewicz_K H (generic_neg C p) (generic_neg C q))
        dnp)) dp.

Arguments generic_lukasiewicz_explosion_raw {S F E C s}
  _ _ _ _ _.

Lemma generic_lukasiewicz_inconsistent_of_provable_neg :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_lukasiewicz_entailment E C s -> forall p,
      generic_provable E s p ->
      generic_provable E s (generic_neg C p) ->
      generic_inconsistent E s.
Proof.
  intros S F E C s H p [dp] [dnp] q. constructor.
  exact (generic_lukasiewicz_explosion_raw H p q dp dnp).
Qed.

(** * Reconstruction from the Lukasiewicz abbreviations *)

Definition generic_lukasiewicz_neg_to_imp_bottom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p : F) :
    generic_proof E s
      (generic_imp C (generic_neg C p)
        (generic_imp C p (generic_bottom C))).
Proof.
  rewrite (generic_lukasiewicz_neg A p).
  exact (generic_lukasiewicz_identity_raw H
    (generic_imp C p (generic_bottom C))).
Defined.

Definition generic_lukasiewicz_imp_bottom_to_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p (generic_bottom C))
        (generic_neg C p)).
Proof.
  rewrite (generic_lukasiewicz_neg A p).
  exact (generic_lukasiewicz_identity_raw H
    (generic_imp C p (generic_bottom C))).
Defined.

Definition generic_lukasiewicz_verum_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) :
    generic_proof E s (generic_top C).
Proof.
  rewrite (generic_lukasiewicz_top A).
  rewrite (generic_lukasiewicz_neg A (generic_bottom C)).
  exact (generic_lukasiewicz_identity_raw H (generic_bottom C)).
Defined.

Definition generic_lukasiewicz_efq_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p : F) :
    generic_proof E s (generic_axiom_efq C p).
Proof.
  assert (dnb : generic_proof E s (generic_neg C (generic_bottom C))).
  { rewrite (generic_lukasiewicz_neg A (generic_bottom C)).
    exact (generic_lukasiewicz_identity_raw H (generic_bottom C)). }
  pose (dnpnb := generic_modus_ponens_raw (generic_lukasiewicz_mdp H)
    (generic_neg C (generic_bottom C))
    (generic_imp C (generic_neg C p) (generic_neg C (generic_bottom C)))
    (generic_lukasiewicz_K H (generic_neg C (generic_bottom C))
      (generic_neg C p)) dnb).
  exact (generic_modus_ponens_raw (generic_lukasiewicz_mdp H)
    (generic_imp C (generic_neg C p) (generic_neg C (generic_bottom C)))
    (generic_imp C (generic_bottom C) p)
    (generic_elim_contra_raw (generic_lukasiewicz_elim_contra H)
      (generic_bottom C) p) dnpnb).
Defined.

Arguments generic_lukasiewicz_efq_raw {S F E C s} _ _ _.

Definition generic_has_axiom_efq_of_lukasiewicz {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) :
    generic_has_axiom_efq E C s :=
  {| generic_efq_raw := generic_lukasiewicz_efq_raw H A |}.

(** Antecedent exchange is shared by the source's disjunction introduction
    and several connective reconstructions. *)
Definition generic_lukasiewicz_imp_swap_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s) (p q r : F)
    (d : generic_proof E s
      (generic_imp C p (generic_imp C q r))) :
    generic_proof E s (generic_imp C q (generic_imp C p r)).
Proof.
  assert (dp : generic_list_derivation E s C [p; q] p).
  { exact (GLD_assumption (GRLM_here [q])). }
  assert (dq : generic_list_derivation E s C [p; q] q).
  { exact (GLD_assumption (GRLM_there p (GRLM_here []))). }
  pose (dr := GLD_mdp (GLD_mdp (GLD_theorem d) dp) dq).
  exact (generic_empty_derivation_raw (generic_lukasiewicz_mdp H)
    (generic_list_deduction (generic_lukasiewicz_mdp H)
      (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
      (generic_list_deduction (generic_lukasiewicz_mdp H)
        (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dr))).
Defined.

Arguments generic_lukasiewicz_imp_swap_raw {S F E C s}
  _ _ _ _ _.

Definition generic_lukasiewicz_explosion_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_neg C p) (generic_imp C p q)).
Proof.
  set (np := generic_neg C p).
  assert (dp : generic_list_derivation E s C [p; np] p).
  { exact (GLD_assumption (GRLM_here [np])). }
  assert (dnp : generic_list_derivation E s C [p; np] np).
  { exact (GLD_assumption (GRLM_there p (GRLM_here []))). }
  pose (dpbot := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_neg_to_imp_bottom_raw H A p)) dnp).
  pose (dbot := GLD_mdp dpbot dp).
  pose (dq := GLD_mdp (GLD_theorem (generic_lukasiewicz_efq_raw H A q)) dbot).
  exact (generic_empty_derivation_raw (generic_lukasiewicz_mdp H)
    (generic_list_deduction (generic_lukasiewicz_mdp H)
      (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
      (generic_list_deduction (generic_lukasiewicz_mdp H)
        (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dq))).
Defined.

Arguments generic_lukasiewicz_explosion_axiom_raw {S F E C s}
  _ _ _ _.

Definition generic_lukasiewicz_contraposition_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p q)
        (generic_imp C (generic_neg C q) (generic_neg C p))).
Proof.
  set (f := generic_imp C p q).
  set (nq := generic_neg C q).
  assert (dp : generic_list_derivation E s C [p; nq; f] p).
  { exact (GLD_assumption (GRLM_here [nq; f])). }
  assert (dnq : generic_list_derivation E s C [p; nq; f] nq).
  { exact (GLD_assumption (GRLM_there p (GRLM_here [f]))). }
  assert (df : generic_list_derivation E s C [p; nq; f] f).
  { exact (GLD_assumption
      (GRLM_there p (GRLM_there nq (GRLM_here [])))). }
  pose (dq := GLD_mdp df dp).
  pose (dqbot := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_neg_to_imp_bottom_raw H A q)) dnq).
  pose (dbot := GLD_mdp dqbot dq).
  pose (dpbot := generic_list_deduction (generic_lukasiewicz_mdp H)
    (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dbot).
  pose (dnp := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_imp_bottom_to_neg_raw H A p)) dpbot).
  exact (generic_empty_derivation_raw (generic_lukasiewicz_mdp H)
    (generic_list_deduction (generic_lukasiewicz_mdp H)
      (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
      (generic_list_deduction (generic_lukasiewicz_mdp H)
        (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dnp))).
Defined.

Arguments generic_lukasiewicz_contraposition_axiom_raw {S F E C s}
  _ _ _ _.

Definition generic_lukasiewicz_contraposition_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F)
    (d : generic_proof E s (generic_imp C p q)) :
    generic_proof E s
      (generic_imp C (generic_neg C q) (generic_neg C p)) :=
  generic_modus_ponens_raw (generic_lukasiewicz_mdp H) _ _
    (generic_lukasiewicz_contraposition_axiom_raw H A p q) d.

Arguments generic_lukasiewicz_contraposition_raw {S F E C s}
  _ _ _ _ _.

Definition generic_lukasiewicz_and1_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s (generic_axiom_and1 C p q).
Proof.
  unfold generic_axiom_and1.
  rewrite (generic_lukasiewicz_and A p q).
  exact (@generic_imp_trans_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_K H)
    (generic_lukasiewicz_S H)
    (generic_neg C (generic_imp C p (generic_neg C q)))
    (generic_neg C (generic_neg C p)) p
    (generic_lukasiewicz_contraposition_raw H A
      (generic_neg C p) (generic_imp C p (generic_neg C q))
      (generic_lukasiewicz_explosion_axiom_raw H A p (generic_neg C q)))
    (generic_lukasiewicz_dne_raw H p)).
Defined.

Definition generic_lukasiewicz_and2_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s (generic_axiom_and2 C p q).
Proof.
  unfold generic_axiom_and2.
  rewrite (generic_lukasiewicz_and A p q).
  exact (@generic_imp_trans_raw S F E C s
    (generic_lukasiewicz_mdp H) (generic_lukasiewicz_K H)
    (generic_lukasiewicz_S H)
    (generic_neg C (generic_imp C p (generic_neg C q)))
    (generic_neg C (generic_neg C q)) q
    (generic_lukasiewicz_contraposition_raw H A
      (generic_neg C q) (generic_imp C p (generic_neg C q))
      (generic_lukasiewicz_K H (generic_neg C q) p))
    (generic_lukasiewicz_dne_raw H q)).
Defined.

Definition generic_lukasiewicz_and3_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s (generic_axiom_and3 C p q).
Proof.
  set (f := generic_imp C p (generic_neg C q)).
  assert (df : generic_list_derivation E s C [f; q; p] f).
  { exact (GLD_assumption (GRLM_here [q; p])). }
  assert (dq : generic_list_derivation E s C [f; q; p] q).
  { exact (GLD_assumption (GRLM_there f (GRLM_here [p]))). }
  assert (dp : generic_list_derivation E s C [f; q; p] p).
  { exact (GLD_assumption
      (GRLM_there f (GRLM_there q (GRLM_here [])))). }
  pose (dnq := GLD_mdp df dp).
  pose (dqbot := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_neg_to_imp_bottom_raw H A q)) dnq).
  pose (dbot := GLD_mdp dqbot dq).
  pose (dfbot := generic_list_deduction (generic_lukasiewicz_mdp H)
    (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dbot).
  pose (dnf := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_imp_bottom_to_neg_raw H A f)) dfbot).
  pose (d := generic_empty_derivation_raw (generic_lukasiewicz_mdp H)
    (generic_list_deduction (generic_lukasiewicz_mdp H)
      (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
      (generic_list_deduction (generic_lukasiewicz_mdp H)
        (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dnf))).
  unfold generic_axiom_and3.
  rewrite (generic_lukasiewicz_and A p q).
  exact d.
Defined.

Definition generic_lukasiewicz_or1_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s (generic_axiom_or1 C p q).
Proof.
  unfold generic_axiom_or1.
  rewrite (generic_lukasiewicz_or A p q).
  exact (generic_lukasiewicz_imp_swap_raw H
    (generic_neg C p) p q
    (generic_lukasiewicz_explosion_axiom_raw H A p q)).
Defined.

Definition generic_lukasiewicz_or2_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q : F) :
    generic_proof E s (generic_axiom_or2 C p q).
Proof.
  unfold generic_axiom_or2.
  rewrite (generic_lukasiewicz_or A p q).
  exact (generic_lukasiewicz_K H q (generic_neg C p)).
Defined.

Definition generic_lukasiewicz_or3_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p q r : F) :
    generic_proof E s (generic_axiom_or3 C p q r).
Proof.
  set (hp := generic_imp C p r).
  set (hq := generic_imp C q r).
  set (np := generic_neg C p).
  set (nr := generic_neg C r).
  set (o := generic_imp C np q).
  assert (dnr : generic_list_derivation E s C [nr; o; hq; hp] nr).
  { exact (GLD_assumption (GRLM_here [o; hq; hp])). }
  assert (dor : generic_list_derivation E s C [nr; o; hq; hp] o).
  { exact (GLD_assumption (GRLM_there nr (GRLM_here [hq; hp]))). }
  assert (dhq : generic_list_derivation E s C [nr; o; hq; hp] hq).
  { exact (GLD_assumption
      (GRLM_there nr (GRLM_there o (GRLM_here [hp])))). }
  assert (dhp : generic_list_derivation E s C [nr; o; hq; hp] hp).
  { exact (GLD_assumption
      (GRLM_there nr (GRLM_there o
        (GRLM_there hq (GRLM_here []))))). }
  pose (dnrnp := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_contraposition_axiom_raw H A p r)) dhp).
  pose (dnp := GLD_mdp dnrnp dnr).
  pose (dq := GLD_mdp dor dnp).
  pose (dr := GLD_mdp dhq dq).
  pose (drbot := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_neg_to_imp_bottom_raw H A r)) dnr).
  pose (dbot := GLD_mdp drbot dr).
  pose (dnrbot := generic_list_deduction (generic_lukasiewicz_mdp H)
    (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dbot).
  pose (dnnr := GLD_mdp
    (GLD_theorem (generic_lukasiewicz_imp_bottom_to_neg_raw H A nr)) dnrbot).
  pose (dr' := GLD_mdp (GLD_theorem (generic_lukasiewicz_dne_raw H r)) dnnr).
  pose (d := generic_empty_derivation_raw (generic_lukasiewicz_mdp H)
    (generic_list_deduction (generic_lukasiewicz_mdp H)
      (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
      (generic_list_deduction (generic_lukasiewicz_mdp H)
        (generic_lukasiewicz_K H) (generic_lukasiewicz_S H)
        (generic_list_deduction (generic_lukasiewicz_mdp H)
          (generic_lukasiewicz_K H) (generic_lukasiewicz_S H) dr')))).
  unfold generic_axiom_or3.
  rewrite (generic_lukasiewicz_or A p q).
  exact d.
Defined.

Definition generic_lukasiewicz_neg_equiv_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) (p : F) :
    generic_proof E s (generic_axiom_neg_equiv C p).
Proof.
  set (x := generic_imp C p (generic_bottom C)).
  pose (dx := generic_lukasiewicz_identity_raw H x).
  pose (d := generic_modus_ponens_raw (generic_lukasiewicz_mdp H) _ _
    (generic_modus_ponens_raw (generic_lukasiewicz_mdp H) _ _
      (generic_lukasiewicz_and3_raw H A
        (generic_imp C x x) (generic_imp C x x)) dx) dx).
  unfold generic_axiom_neg_equiv, generic_formula_iff.
  rewrite (generic_lukasiewicz_neg A p).
  exact d.
Defined.

Definition generic_classical_of_lukasiewicz {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_lukasiewicz_entailment E C s)
    (A : generic_lukasiewicz_abbrev C) :
    generic_classical_entailment E C s.
Proof.
  constructor.
  - exact (generic_lukasiewicz_mdp H).
  - exact (generic_lukasiewicz_neg_equiv_raw H A).
  - exact (generic_lukasiewicz_verum_raw H A).
  - exact (generic_lukasiewicz_K H).
  - exact (generic_lukasiewicz_S H).
  - exact (generic_lukasiewicz_and1_raw H A).
  - exact (generic_lukasiewicz_and2_raw H A).
  - exact (generic_lukasiewicz_and3_raw H A).
  - exact (generic_lukasiewicz_or1_raw H A).
  - exact (generic_lukasiewicz_or2_raw H A).
  - exact (generic_lukasiewicz_or3_raw H A).
  - exact (generic_lukasiewicz_dne_raw H).
Defined.
