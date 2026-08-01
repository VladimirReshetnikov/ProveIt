(** Gödel--Gentzen negative translation from classical NNF formulas into
    intuitionistic first-order formulas. *)

From Stdlib Require Import Lists.List Vectors.Fin.
From FoundationModal Require Import GenericCalculus
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew Deduction.
From Foundation.FirstOrder.Basic Require Import Calculus.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The translation is defined for arbitrary free-variable types and binder
    arities.  Thus all substitution and embedding laws below are instances of
    one capture-avoiding rewrite theorem. *)
Fixpoint ifo_double_negation_translation {L X n}
    (phi : semiformula L X n) : ifo_semiformula L X n :=
  match phi with
  | Semiformula_verum _ => ifo_verum
  | Semiformula_falsum _ => IFOFalsum
  | Semiformula_rel R v => ifo_neg (ifo_neg (IFORel R v))
  | Semiformula_nrel R v => ifo_neg (IFORel R v)
  | Semiformula_and psi chi =>
      IFOAnd (ifo_double_negation_translation psi)
        (ifo_double_negation_translation chi)
  | Semiformula_or psi chi =>
      ifo_neg
        (IFOAnd (ifo_neg (ifo_double_negation_translation psi))
          (ifo_neg (ifo_double_negation_translation chi)))
  | Semiformula_all psi =>
      IFOAll (ifo_double_negation_translation psi)
  | Semiformula_exists psi =>
      ifo_neg (IFOAll (ifo_neg (ifo_double_negation_translation psi)))
  end.

Lemma ifo_double_negation_rel : forall L X n k
    (R : language_rel L k) v,
  ifo_double_negation_translation (@Semiformula_rel L X n k R v) =
  ifo_neg (ifo_neg (IFORel R v)).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_nrel : forall L X n k
    (R : language_rel L k) v,
  ifo_double_negation_translation (@Semiformula_nrel L X n k R v) =
  ifo_neg (IFORel R v).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_verum : forall L X n,
  ifo_double_negation_translation (@Semiformula_verum L X n) = ifo_verum.
Proof. reflexivity. Qed.

Lemma ifo_double_negation_falsum : forall L X n,
  ifo_double_negation_translation (@Semiformula_falsum L X n) = IFOFalsum.
Proof. reflexivity. Qed.

Lemma ifo_double_negation_and : forall L X n
    (phi psi : semiformula L X n),
  ifo_double_negation_translation (Semiformula_and phi psi) =
  IFOAnd (ifo_double_negation_translation phi)
    (ifo_double_negation_translation psi).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_or : forall L X n
    (phi psi : semiformula L X n),
  ifo_double_negation_translation (Semiformula_or phi psi) =
  ifo_neg
    (IFOAnd (ifo_neg (ifo_double_negation_translation phi))
      (ifo_neg (ifo_double_negation_translation psi))).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_all : forall L X n
    (phi : semiformula L X (S n)),
  ifo_double_negation_translation (Semiformula_all phi) =
  IFOAll (ifo_double_negation_translation phi).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_exists : forall L X n
    (phi : semiformula L X (S n)),
  ifo_double_negation_translation (Semiformula_exists phi) =
  ifo_neg (IFOAll (ifo_neg (ifo_double_negation_translation phi))).
Proof. reflexivity. Qed.

Lemma ifo_double_negation_imp : forall L X n
    (phi psi : semiformula L X n),
  ifo_double_negation_translation (semiformula_imp phi psi) =
  ifo_neg
    (IFOAnd
      (ifo_neg (ifo_double_negation_translation (semiformula_neg phi)))
      (ifo_neg (ifo_double_negation_translation psi))).
Proof. reflexivity. Qed.

Theorem ifo_double_negation_negative : forall L X n
    (phi : semiformula L X n),
  ifo_negative n (ifo_double_negation_translation phi).
Proof.
  intros L X n phi. induction phi; simpl.
  - apply ifo_negative_verum.
  - constructor.
  - apply ifo_negative_neg.
  - apply ifo_negative_neg.
  - now constructor.
  - apply ifo_negative_neg.
  - now constructor.
  - apply ifo_negative_neg.
Qed.

(** Exact [List.conj2] presentations for the source and target syntaxes.
    The singleton case deliberately avoids a redundant conjunction with top. *)
Fixpoint semiformula_list_conj2 {L X n}
    (Gamma : list (semiformula L X n)) : semiformula L X n :=
  match Gamma with
  | [] => Semiformula_verum n
  | [phi] => phi
  | phi :: rest => Semiformula_and phi (semiformula_list_conj2 rest)
  end.

Fixpoint ifo_list_conj2 {L X n}
    (Gamma : list (ifo_semiformula L X n)) : ifo_semiformula L X n :=
  match Gamma with
  | [] => ifo_verum
  | [phi] => phi
  | phi :: rest => IFOAnd phi (ifo_list_conj2 rest)
  end.

Theorem ifo_double_negation_list_conj2 : forall L X n
    (Gamma : list (semiformula L X n)),
  ifo_double_negation_translation (semiformula_list_conj2 Gamma) =
  ifo_list_conj2 (map ifo_double_negation_translation Gamma).
Proof.
  intros L X n Gamma. induction Gamma as [|phi Gamma IH].
  - reflexivity.
  - destruct Gamma as [|psi Gamma].
    + reflexivity.
    + cbn [semiformula_list_conj2 ifo_list_conj2
        ifo_double_negation_translation List.map].
      f_equal. exact IH.
Qed.

Theorem ifo_rewrite_double_negation : forall L X n Y m
    (w : rew L X n Y m) (phi : semiformula L X n),
  ifo_rewrite w (ifo_double_negation_translation phi) =
  ifo_double_negation_translation (semiformula_rewrite w phi).
Proof.
  intros L X n Y m w phi. revert Y m w.
  induction phi; intros Y m w; simpl; try reflexivity.
  - now rewrite (IHphi1 Y m w), (IHphi2 Y m w).
  - now rewrite (IHphi1 Y m w), (IHphi2 Y m w).
  - now rewrite (IHphi Y (S m) (rew_q w)).
  - now rewrite (IHphi Y (S m) (rew_q w)).
Qed.

Corollary ifo_substitute_double_negation : forall L X n m
    (phi : semiformula L X n) (v : Fin.t n -> semiterm L X m),
  ifo_substitute v (ifo_double_negation_translation phi) =
  ifo_double_negation_translation (semiformula_substitute v phi).
Proof. intros. apply ifo_rewrite_double_negation. Qed.

Corollary ifo_emb_double_negation : forall L X n
    (phi : semisentence L n),
  @ifo_emb L Empty_set X n ifo_empty_elim
    (ifo_double_negation_translation phi) =
  ifo_double_negation_translation
    (semiformula_rewrite
      (@rew_emb L Empty_set X n ifo_empty_elim) phi).
Proof. intros. apply ifo_rewrite_double_negation. Qed.

(** Pointwise sequent translation. *)
Definition ifo_double_negation_sequent {L}
    (Gamma : first_order_sequent L) : list (ifo_proposition L) :=
  map ifo_double_negation_translation Gamma.

Lemma ifo_double_negation_sequent_nil : forall L,
  @ifo_double_negation_sequent L [] = [].
Proof. reflexivity. Qed.

Lemma ifo_double_negation_sequent_cons : forall L
    (phi : proposition L) Gamma,
  ifo_double_negation_sequent (phi :: Gamma) =
  ifo_double_negation_translation phi :: ifo_double_negation_sequent Gamma.
Proof. reflexivity. Qed.

Lemma ifo_double_negation_sequent_append : forall L
    (Gamma Delta : first_order_sequent L),
  ifo_double_negation_sequent (Gamma ++ Delta) =
  ifo_double_negation_sequent Gamma ++ ifo_double_negation_sequent Delta.
Proof. intros. unfold ifo_double_negation_sequent. apply map_app. Qed.

Theorem ifo_shift_double_negation_sequent : forall L
    (Gamma : first_order_sequent L),
  map ifo_shift (ifo_double_negation_sequent Gamma) =
  ifo_double_negation_sequent (first_order_sequent_shift Gamma).
Proof.
  intros L Gamma. induction Gamma as [|phi Gamma IH]; simpl.
  - reflexivity.
  - unfold ifo_shift, semiformula_shift in *. simpl.
    now rewrite ifo_rewrite_double_negation, IH.
Qed.

(** A proof-relevant image of a classical sentence theory.  This strictly
    contains the source's Prop-valued image while retaining the originating
    axiom and its equality witness for downstream proof transport. *)
Definition ifo_double_negation_theory {L} (T : theory L) : ifo_theory L :=
  {| ifo_theory_axiom := fun phi =>
      { psi : sentence L &
        (T psi * (ifo_double_negation_translation psi = phi))%type } |}.

Lemma ifo_double_negation_theory_axiom_eq : forall L
    (T : theory L) (phi : ifo_sentence L),
  ifo_theory_axiom (ifo_double_negation_theory T) phi =
  { psi : sentence L &
    (T psi * (ifo_double_negation_translation psi = phi))%type }.
Proof. reflexivity. Qed.

Definition ifo_double_negation_theory_intro {L} {T : theory L}
    {psi : sentence L} (Hpsi : T psi) :
    ifo_theory_axiom (ifo_double_negation_theory T)
      (ifo_double_negation_translation psi) :=
  existT _ psi (Hpsi, eq_refl).

Definition ifo_double_negation_theory_source {L} {T : theory L}
    {phi : ifo_sentence L}
    (Hphi : ifo_theory_axiom (ifo_double_negation_theory T) phi) :
    { psi : sentence L &
      (T psi * (ifo_double_negation_translation psi = phi))%type } := Hphi.

(** Negation commutes with the translation up to intuitionistic equivalence.
    The rewrite-parametric formulation is structurally recursive on the
    source formula; the source module only states its closed-proposition
    specialization and therefore needs a separate complexity argument in the
    quantified cases. *)
Fixpoint ifo_hilbert_neg_double_negation_rewrite {L H X n}
    (phi : semiformula L X n) {struct phi} :
    forall w : rew L X n nat 0,
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp
          (ifo_neg
            (ifo_double_negation_translation
              (semiformula_rewrite w phi)))
          (ifo_double_negation_translation
            (semiformula_rewrite w (semiformula_neg phi))))
        (IFOImp
          (ifo_double_negation_translation
            (semiformula_rewrite w (semiformula_neg phi)))
          (ifo_neg
            (ifo_double_negation_translation
              (semiformula_rewrite w phi))))).
Proof.
  destruct phi as [n | n | n k R v | n k R v |
    n phi psi | n phi psi | n phi | n phi]; intro w; simpl.
  - exact (generic_minimal_double_neg_bottom_iff_raw
      (ifo_hilbert_minimal_capability H)).
  - exact (generic_minimal_iff_refl_raw
      (ifo_hilbert_minimal_capability H) (ifo_neg IFOFalsum)).
  - exact (generic_minimal_triple_neg_iff_raw
      (ifo_hilbert_minimal_capability H)
      (IFORel R (fun i => rew_apply w (v i)))).
  - exact (generic_minimal_iff_refl_raw
      (ifo_hilbert_minimal_capability H)
      (ifo_neg (ifo_neg (IFORel R (fun i => rew_apply w (v i)))))).
  - pose (Hm := ifo_hilbert_minimal_capability H).
    pose (ihphi := @ifo_hilbert_neg_double_negation_rewrite
      L H X n phi w).
    pose (ihpsi := @ifo_hilbert_neg_double_negation_rewrite
      L H X n psi w).
    pose (ephi := ifo_hilbert_iff_neg_of_neg_iff
      (phi := ifo_double_negation_translation (semiformula_rewrite w phi))
      (psi := ifo_double_negation_translation
        (semiformula_rewrite w (semiformula_neg phi)))
      (ifo_double_negation_negative (semiformula_rewrite w phi)) ihphi).
    pose (epsi := ifo_hilbert_iff_neg_of_neg_iff
      (phi := ifo_double_negation_translation (semiformula_rewrite w psi))
      (psi := ifo_double_negation_translation
        (semiformula_rewrite w (semiformula_neg psi)))
      (ifo_double_negation_negative (semiformula_rewrite w psi)) ihpsi).
    exact (generic_minimal_neg_iff_congr_raw Hm _ _
      (generic_minimal_and_iff_congr_raw Hm _ _ _ _ ephi epsi)).
  - pose (Hm := ifo_hilbert_minimal_capability H).
    pose (ihphi := @ifo_hilbert_neg_double_negation_rewrite
      L H X n phi w).
    pose (ihpsi := @ifo_hilbert_neg_double_negation_rewrite
      L H X n psi w).
    set (a := IFOAnd
      (ifo_neg (ifo_double_negation_translation
        (semiformula_rewrite w phi)))
      (ifo_neg (ifo_double_negation_translation
        (semiformula_rewrite w psi)))).
    pose (da := @ifo_hilbert_double_neg_iff_negative L H a
      (IFONegativeAnd (ifo_negative_neg _) (ifo_negative_neg _))).
    exact (generic_minimal_iff_trans_raw Hm _ a _ da
      (generic_minimal_and_iff_congr_raw Hm _ _ _ _ ihphi ihpsi)).
  - pose (Hm := ifo_hilbert_minimal_capability H).
    set (a := ifo_double_negation_translation
      (semiformula_rewrite (rew_q w) phi)).
    set (b := ifo_double_negation_translation
      (semiformula_rewrite (rew_q w) (semiformula_neg phi))).
    pose (ihfree := @ifo_hilbert_neg_double_negation_rewrite
      L H X (S n) phi (rew_comp (@rew_free L 0) (rew_q w))).
    rewrite !semiformula_rewrite_comp in ihfree.
    assert (ihfree' : @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (ifo_neg (@ifo_free L 0 a)) (@ifo_free L 0 b))
        (IFOImp (@ifo_free L 0 b) (ifo_neg (@ifo_free L 0 a))))).
    { unfold a, b, ifo_free.
      rewrite !ifo_rewrite_double_negation. exact ihfree. }
    pose (efree := ifo_hilbert_iff_neg_of_neg_iff
      (phi := @ifo_free L 0 a) (psi := @ifo_free L 0 b)
      (proj2 (ifo_negative_rewrite_iff (@rew_free L 0) a)
        (ifo_double_negation_negative
          (semiformula_rewrite (rew_q w) phi))) ihfree').
    assert (efree' : @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (@ifo_free L 0 a) (@ifo_free L 0 (ifo_neg b)))
        (IFOImp (@ifo_free L 0 (ifo_neg b)) (@ifo_free L 0 a)))).
    { exact efree. }
    pose (eall := ifo_hilbert_all_iff_all_of_free_iff
      (phi := a) (psi := ifo_neg b) efree').
    exact (generic_minimal_neg_iff_congr_raw Hm _ _ eall).
  - pose (Hm := ifo_hilbert_minimal_capability H).
    set (a := ifo_double_negation_translation
      (semiformula_rewrite (rew_q w) phi)).
    set (b := ifo_double_negation_translation
      (semiformula_rewrite (rew_q w) (semiformula_neg phi))).
    pose (ihfree := @ifo_hilbert_neg_double_negation_rewrite
      L H X (S n) phi (rew_comp (@rew_free L 0) (rew_q w))).
    rewrite !semiformula_rewrite_comp in ihfree.
    assert (ihfree' : @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (@ifo_free L 0 (ifo_neg a)) (@ifo_free L 0 b))
        (IFOImp (@ifo_free L 0 b) (@ifo_free L 0 (ifo_neg a))))).
    { unfold a, b, ifo_free.
      rewrite !ifo_rewrite_neg, !ifo_rewrite_double_negation. exact ihfree. }
    pose (eall := ifo_hilbert_all_iff_all_of_free_iff
      (phi := ifo_neg a) (psi := b) ihfree').
    pose (dne := @ifo_hilbert_double_neg_iff_negative L H
      (IFOAll (ifo_neg a))
      (IFONegativeAll (ifo_negative_neg _))).
    exact (generic_minimal_iff_trans_raw Hm _ _ _ dne eall).
Defined.

Definition ifo_hilbert_neg_double_negation {L H}
    (phi : proposition L) :
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (ifo_neg (ifo_double_negation_translation phi))
          (ifo_double_negation_translation (semiformula_neg phi)))
        (IFOImp (ifo_double_negation_translation (semiformula_neg phi))
          (ifo_neg (ifo_double_negation_translation phi)))).
Proof.
  refine (ifo_hilbert_proof_cast
    (@ifo_hilbert_neg_double_negation_rewrite L H nat 0 phi rew_id) _).
  now rewrite !semiformula_rewrite_id.
Defined.

Definition ifo_hilbert_neg_neg_double_negation {L H}
    (phi : proposition L) :
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp
          (ifo_neg
            (ifo_double_negation_translation (semiformula_neg phi)))
          (ifo_double_negation_translation phi))
        (IFOImp (ifo_double_negation_translation phi)
          (ifo_neg
            (ifo_double_negation_translation (semiformula_neg phi))))).
Proof.
  refine (ifo_hilbert_proof_cast
    (@ifo_hilbert_neg_double_negation L H (semiformula_neg phi)) _).
  now rewrite semiformula_neg_involutive.
Defined.

(** On a weak-negative consequent, implication is equivalent to refuting the
    antecedent conjoined with the negated consequent.  This is the stable
    propositional core of the translated classical implication. *)
Definition ifo_hilbert_imp_iff_neg_and_negative {L H}
    (phi psi : ifo_proposition L) (hpsi : ifo_negative 0 psi) :
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (IFOImp phi psi)
          (ifo_neg (IFOAnd phi (ifo_neg psi))))
        (IFOImp (ifo_neg (IFOAnd phi (ifo_neg psi)))
          (IFOImp phi psi))).
Proof.
  pose (Hm := ifo_hilbert_minimal_capability H).
  apply (generic_minimal_iff_intro_raw Hm).
  - exact (generic_minimal_imp_to_neg_and_axiom_raw Hm phi psi).
  - set (Gamma := [ifo_neg psi; phi; ifo_neg (IFOAnd phi (ifo_neg psi))]).
    assert (dnq : @ifo_context_derivation L H Gamma (ifo_neg psi)).
    { apply ifo_context_assumption. unfold Gamma. exact (GRLM_here _). }
    assert (dp : @ifo_context_derivation L H Gamma phi).
    { apply ifo_context_assumption. unfold Gamma.
      exact (GRLM_there _ (GRLM_here _)). }
    assert (dna : @ifo_context_derivation L H Gamma
        (ifo_neg (IFOAnd phi (ifo_neg psi)))).
    { apply ifo_context_assumption. unfold Gamma.
      exact (GRLM_there _ (GRLM_there _ (GRLM_here _))). }
    pose (dand := ifo_context_mdp
      (ifo_context_mdp
        (ifo_context_theorem (Gamma := Gamma) (IFOHPAnd3 phi (ifo_neg psi)))
        dp) dnq).
    pose (dbot := ifo_context_mdp dna dand).
    pose (dnnq := ifo_context_deduct dbot).
    pose (dq := ifo_context_mdp
      (ifo_context_theorem (Gamma := [phi; ifo_neg (IFOAnd phi (ifo_neg psi))])
        (@ifo_hilbert_dne_negative L H psi hpsi)) dnnq).
    exact (generic_empty_derivation_raw (ifo_hilbert_modus_ponens H)
      (ifo_context_deduct (ifo_context_deduct dq))).
Defined.

Definition ifo_hilbert_imp_double_negation {L H}
    (phi psi : proposition L) :
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp
          (IFOImp (ifo_double_negation_translation phi)
            (ifo_double_negation_translation psi))
          (ifo_double_negation_translation
            (semiformula_imp phi psi)))
        (IFOImp
          (ifo_double_negation_translation
            (semiformula_imp phi psi))
          (IFOImp (ifo_double_negation_translation phi)
            (ifo_double_negation_translation psi)))).
Proof.
  pose (Hm := ifo_hilbert_minimal_capability H).
  set (p := ifo_double_negation_translation phi).
  set (q := ifo_double_negation_translation psi).
  set (np := ifo_double_negation_translation (semiformula_neg phi)).
  pose (ebase := ifo_hilbert_imp_iff_neg_and_negative
    (H := H) p (psi := q)
    (ifo_double_negation_negative psi)).
  pose (enp := @ifo_hilbert_neg_neg_double_negation L H phi).
  pose (einside := generic_minimal_and_iff_congr_raw Hm
    p (ifo_neg np) (ifo_neg q) (ifo_neg q)
    (generic_minimal_iff_symm_raw Hm _ _ enp)
    (generic_minimal_iff_refl_raw Hm (ifo_neg q))).
  pose (eneg := generic_minimal_neg_iff_congr_raw Hm _ _ einside).
  exact (generic_minimal_iff_trans_raw Hm _ _ _ ebase eneg).
Defined.
