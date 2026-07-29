(** The generic implicational core of the classical Lukasiewicz basis.

    Foundation's [Propositional/Entailment/Cl/Łukasiewicz.lean] starts with
    modus ponens, K, S, and elimination of contraposition, then reconstructs
    classical reasoning.  The principal DNE, DNI, and explosion results below
    need no assumptions about conjunction, disjunction, truth, or formula
    equality, so their capability records only that exact boundary.
*)

From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms.

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
