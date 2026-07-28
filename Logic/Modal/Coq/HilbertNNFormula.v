(**
  Hilbert-K normalization into negation-normal modal formulas.

  This file independently ports the complete three-declaration active
  surface of the pinned Foundation module [Modal/Hilbert/NNFormula.lean].
  The source proves the equivalences by detailed Hilbert derivations.  Here
  the already checked NNF truth theorems and K completeness give shorter,
  representation-independent proofs.
*)

From FoundationModal Require Import
  Syntax NNFormula Kripke NNFormulaSemantics HilbertK HilbertKSoundness
  CanonicalK.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** NNF negation represents ordinary negation up to provable K-equivalence. *)
Theorem K_proves_nnformula_iff_neg :
  forall p : nnformula nat,
    K_proves (Iff (Neg (nn_to_formula p))
                  (nn_to_formula (nn_neg p))).
Proof.
  intro p. apply K_complete. intros F V w.
  apply (proj2 (@satisfies_iff nat F V w
    (Neg (nn_to_formula p)) (nn_to_formula (nn_neg p)))).
  rewrite satisfies_neg.
  rewrite <- (@nn_to_formula_correct nat F V w p).
  rewrite <- (@nn_to_formula_correct nat F V w (nn_neg p)).
  pose proof (@nn_satisfies_neg nat F V w p).
  tauto.
Qed.

(** Every ordinary modal formula has a provably equivalent NNF
    representative. *)
Theorem K_proves_exists_nnformula_iff :
  forall p : formula nat,
    exists q : nnformula nat,
      K_proves (Iff p (nn_to_formula q)).
Proof.
  intro p. exists (formula_to_nnf p).
  apply K_complete. intros F V w.
  apply (proj2 (@satisfies_iff nat F V w p
    (nn_to_formula (formula_to_nnf p)))).
  symmetry. apply formula_nnf_round_trip.
Qed.

(** A provable formula therefore has a provable NNF representative. *)
Theorem K_proves_exists_nnformula_of_provable :
  forall p : formula nat,
    K_proves p ->
    exists q : nnformula nat, K_proves (nn_to_formula q).
Proof.
  intros p Hp. exists (formula_to_nnf p).
  apply K_complete. intros F V w.
  apply (proj2 (@formula_nnf_round_trip nat F V w p)).
  exact (@K_proves_sound_on_frame nat F p Hp V w).
Qed.
