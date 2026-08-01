(** Gödel--Gentzen negative translation from classical NNF formulas into
    intuitionistic first-order formulas. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Program.Equality Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus
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

(** Context used by the recursive translation: every classical sequent
    formula is first structurally negated and then negatively translated. *)
Definition ifo_goedel_gentzen_formula {L} (phi : proposition L) :
    ifo_proposition L :=
  ifo_double_negation_translation (semiformula_neg phi).

Definition ifo_goedel_gentzen_context {L}
    (Gamma : first_order_sequent L) : list (ifo_proposition L) :=
  map ifo_goedel_gentzen_formula Gamma.

Lemma ifo_goedel_gentzen_context_nil : forall L,
  @ifo_goedel_gentzen_context L [] = [].
Proof. reflexivity. Qed.

Lemma ifo_goedel_gentzen_context_cons : forall L
    (phi : proposition L) Gamma,
  ifo_goedel_gentzen_context (phi :: Gamma) =
  ifo_goedel_gentzen_formula phi :: ifo_goedel_gentzen_context Gamma.
Proof. reflexivity. Qed.

Lemma ifo_goedel_gentzen_context_append : forall L
    (Gamma Delta : first_order_sequent L),
  ifo_goedel_gentzen_context (Gamma ++ Delta) =
  ifo_goedel_gentzen_context Gamma ++ ifo_goedel_gentzen_context Delta.
Proof. intros. unfold ifo_goedel_gentzen_context. apply map_app. Qed.

Lemma ifo_free_double_negation : forall L
    (phi : semiproposition L 1),
  @ifo_free L 0 (ifo_double_negation_translation phi) =
  ifo_double_negation_translation (@semiformula_free L 0 phi).
Proof.
  intros L phi. unfold ifo_free, semiformula_free.
  apply ifo_rewrite_double_negation.
Qed.

Lemma ifo_shift_goedel_gentzen_formula : forall L
    (phi : proposition L),
  ifo_shift (ifo_goedel_gentzen_formula phi) =
  ifo_goedel_gentzen_formula (semiformula_shift phi).
Proof.
  intros L phi. unfold ifo_goedel_gentzen_formula,
    ifo_shift, semiformula_shift.
  rewrite ifo_rewrite_double_negation, semiformula_rewrite_neg.
  reflexivity.
Qed.

Theorem ifo_shift_goedel_gentzen_context : forall L
    (Gamma : first_order_sequent L),
  map ifo_shift (ifo_goedel_gentzen_context Gamma) =
  ifo_goedel_gentzen_context (first_order_sequent_shift Gamma).
Proof.
  intros L Gamma. induction Gamma as [|phi Gamma IH]; simpl.
  - reflexivity.
  - now rewrite ifo_shift_goedel_gentzen_formula, IH.
Qed.

Definition ifo_context_cast_context {L H Gamma Delta phi}
    (d : @ifo_context_derivation L H Gamma phi) (e : Gamma = Delta) :
    @ifo_context_derivation L H Delta phi :=
  match e with eq_refl => d end.

(** Turn propositional list membership into a proof-relevant positional
    witness when equality is decidable.  This isolates the sole role of the
    source module's decidable-language assumption in contraction. *)
Fixpoint ifo_raw_member_of_member_dec {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A) (xs : list A) {struct xs} :
    generic_list_member x xs -> generic_raw_list_member x xs.
Proof.
  destruct xs as [|y ys]; intro h.
  - exact (False_rect _ h).
  - destruct (eq_dec x y) as [e | ne].
    + subst y. exact (GRLM_here ys).
    + apply (GRLM_there y).
      apply (@ifo_raw_member_of_member_dec A eq_dec x ys).
      assert (htail : generic_list_member x ys).
      { destruct h as [hxy | htail]; [contradiction | exact htail]. }
      exact htail.
Defined.

Fixpoint ifo_member_of_raw_member {A : Type} {x : A} {xs : list A}
    (h : generic_raw_list_member x xs) : generic_list_member x xs :=
  match h with
  | GRLM_here _ => or_introl eq_refl
  | GRLM_there _ htail => or_intror (ifo_member_of_raw_member htail)
  end.

Fixpoint ifo_raw_map_member_preimage {A B : Type} (f : A -> B)
    (xs : list A) {y : B}
    (h : generic_raw_list_member y (map f xs)) {struct xs} :
    { x : A & (generic_raw_list_member x xs * (f x = y))%type }.
Proof.
  destruct xs as [|x xs].
  - inversion h.
  - dependent destruction h.
    + exists x. split; [exact (GRLM_here xs) | reflexivity].
    + destruct (@ifo_raw_map_member_preimage A B f xs y h)
        as [z [hz ez]].
      exists z. split; [exact (GRLM_there x hz) | exact ez].
Defined.

Definition ifo_raw_member_cast {A : Type} {x y : A} {xs : list A}
    (e : x = y) (h : generic_raw_list_member x xs) :
    generic_raw_list_member y xs :=
  match e with eq_refl => h end.

Definition ifo_goedel_gentzen_context_subset {L}
    (D : language_decidable_eq L)
    {Gamma Delta : first_order_sequent L}
    (incl : generic_list_subset Gamma Delta) :
    forall p,
      generic_raw_list_member p (ifo_goedel_gentzen_context Gamma) ->
      generic_raw_list_member p (ifo_goedel_gentzen_context Delta).
Proof.
  intros p hp.
  destruct (@ifo_raw_map_member_preimage
    (proposition L) (ifo_proposition L)
    (@ifo_goedel_gentzen_formula L) Gamma p hp)
    as [phi [hphi ephi]].
  pose (hDelta := incl phi (ifo_member_of_raw_member hphi)).
  pose (rawDelta := @ifo_raw_member_of_member_dec
    (proposition L) (semiformula_eq_dec D Nat.eq_dec)
    phi Delta hDelta).
  exact (ifo_raw_member_cast ephi
    (generic_raw_list_member_map ifo_goedel_gentzen_formula rawDelta)).
Defined.

(** Recursive Gödel--Gentzen translation of the complete eight-constructor
    one-sided first-order LK calculus. *)
Fixpoint ifo_goedel_gentzen {L H}
    (D : language_decidable_eq L) {Gamma : first_order_sequent L}
    (d : first_order_derivation L Gamma) {struct d} :
    @ifo_context_derivation L H (ifo_goedel_gentzen_context Gamma)
      IFOFalsum.
Proof.
  destruct d as [k R v | phi Gamma Delta dp dn |
    Gamma Delta d incl | | phi psi Gamma d |
    phi psi Gamma dphi dpsi | phi Gamma d | phi t Gamma d].
  - cbn [ifo_goedel_gentzen_context ifo_goedel_gentzen_formula].
    exact (ifo_context_mdp
      (ifo_context_assumption
        (GRLM_there (ifo_neg (IFORel R v)) (GRLM_here [])))
      (ifo_context_assumption (GRLM_here [_]))).
  - pose (ihp := @ifo_goedel_gentzen L H D (phi :: Gamma) dp).
    pose (ihn0 := @ifo_goedel_gentzen L H D
      (semiformula_neg phi :: Delta) dn).
    pose (dntp := ifo_context_deduct ihp).
    assert (econtext :
        ifo_goedel_gentzen_context (semiformula_neg phi :: Delta) =
        ifo_double_negation_translation phi ::
          ifo_goedel_gentzen_context Delta).
    { unfold ifo_goedel_gentzen_context. simpl. f_equal.
      unfold ifo_goedel_gentzen_formula.
      now rewrite semiformula_neg_involutive. }
    pose (ihn := ifo_context_cast_context ihn0 econtext).
    pose (dnt := ifo_context_deduct ihn).
    pose (Hm := ifo_hilbert_minimal_capability H).
    pose (eneg := @ifo_hilbert_neg_double_negation L H phi).
    pose (dleft := generic_minimal_iff_elim_left_raw Hm _ _ eneg).
    pose (dcontra := generic_minimal_contraposition_raw Hm _ _ dleft).
    pose (dnntp := ifo_context_mdp
      (ifo_context_theorem
        (Gamma := ifo_goedel_gentzen_context Gamma) dcontra) dntp).
    assert (eappend :
        ifo_goedel_gentzen_context (Gamma ++ Delta) =
        ifo_goedel_gentzen_context Gamma ++
          ifo_goedel_gentzen_context Delta).
    { apply ifo_goedel_gentzen_context_append. }
    refine (ifo_context_cast_context _ (eq_sym eappend)).
    exact (ifo_context_mdp
      (ifo_context_weaken
        (fun p hp => generic_raw_list_member_app_left _ hp) dnntp)
      (ifo_context_weaken
        (fun p hp => generic_raw_list_member_app_right _ hp) dnt)).
  - exact (ifo_context_weaken
      (ifo_goedel_gentzen_context_subset D incl)
      (@ifo_goedel_gentzen L H D Gamma d)).
  - cbn [ifo_goedel_gentzen_context ifo_goedel_gentzen_formula].
    exact (ifo_context_assumption (GRLM_here [])).
  - pose (ih := @ifo_goedel_gentzen L H D
      (phi :: psi :: Gamma) d).
    pose (dphi := ifo_context_deduct ih).
    pose (dpsi := ifo_context_deduct dphi).
    set (head := ifo_goedel_gentzen_formula (Semiformula_or phi psi)).
    set (tail := ifo_goedel_gentzen_context Gamma).
    assert (dhead : @ifo_context_derivation L H (head :: tail)
        (IFOAnd (ifo_goedel_gentzen_formula phi)
          (ifo_goedel_gentzen_formula psi))).
    { apply ifo_context_assumption. unfold head, tail,
        ifo_goedel_gentzen_formula. simpl. exact (GRLM_here _). }
    pose (dleft := ifo_context_mdp
      (ifo_context_theorem (Gamma := head :: tail)
        (IFOHPAnd1 (ifo_goedel_gentzen_formula phi)
          (ifo_goedel_gentzen_formula psi))) dhead).
    pose (dright := ifo_context_mdp
      (ifo_context_theorem (Gamma := head :: tail)
        (IFOHPAnd2 (ifo_goedel_gentzen_formula phi)
          (ifo_goedel_gentzen_formula psi))) dhead).
    pose (dimp := ifo_context_weaken
      (fun p hp => GRLM_there head hp) dpsi).
    change (@ifo_context_derivation L H (head :: tail) IFOFalsum).
    exact (ifo_context_mdp (ifo_context_mdp dimp dright) dleft).
  - pose (ihphi := @ifo_goedel_gentzen L H D
      (phi :: Gamma) dphi).
    pose (ihpsi := @ifo_goedel_gentzen L H D
      (psi :: Gamma) dpsi).
    pose (dnphi := ifo_context_deduct ihphi).
    pose (dnpsi := ifo_context_deduct ihpsi).
    set (head := ifo_goedel_gentzen_formula (Semiformula_and phi psi)).
    set (tail := ifo_goedel_gentzen_context Gamma).
    assert (dand : @ifo_context_derivation L H tail
        (IFOAnd (ifo_neg (ifo_goedel_gentzen_formula phi))
          (ifo_neg (ifo_goedel_gentzen_formula psi)))).
    { exact (ifo_context_mdp
        (ifo_context_mdp
          (ifo_context_theorem (Gamma := tail)
            (IFOHPAnd3 (ifo_neg (ifo_goedel_gentzen_formula phi))
              (ifo_neg (ifo_goedel_gentzen_formula psi)))) dnphi) dnpsi). }
    assert (dhead : @ifo_context_derivation L H (head :: tail)
        (ifo_neg
          (IFOAnd (ifo_neg (ifo_goedel_gentzen_formula phi))
            (ifo_neg (ifo_goedel_gentzen_formula psi))))).
    { apply ifo_context_assumption. unfold head, tail,
        ifo_goedel_gentzen_formula. simpl. exact (GRLM_here _). }
    change (@ifo_context_derivation L H (head :: tail) IFOFalsum).
    exact (ifo_context_mdp dhead
      (ifo_context_weaken (fun p hp => GRLM_there head hp) dand)).
  - set (body := ifo_double_negation_translation (semiformula_neg phi)).
    pose (ih0 := @ifo_goedel_gentzen L H D
      (@semiformula_free L 0 phi :: first_order_sequent_shift Gamma) d).
    assert (ehead :
        ifo_goedel_gentzen_formula (@semiformula_free L 0 phi) =
        @ifo_free L 0 body).
    { unfold body, ifo_goedel_gentzen_formula.
      rewrite ifo_free_double_negation, semiformula_free_neg.
      reflexivity. }
    assert (econtext :
        ifo_goedel_gentzen_context
          (@semiformula_free L 0 phi :: first_order_sequent_shift Gamma) =
        @ifo_free L 0 body ::
          map ifo_shift (ifo_goedel_gentzen_context Gamma)).
    { unfold ifo_goedel_gentzen_context. simpl. f_equal.
      - exact ehead.
      - symmetry. apply ifo_shift_goedel_gentzen_context. }
    pose (ih := ifo_context_cast_context ih0 econtext).
    pose (dnfree := ifo_context_deduct ih).
    assert (dnfree' : @ifo_context_derivation L H
        (map ifo_shift (ifo_goedel_gentzen_context Gamma))
        (@ifo_free L 0 (ifo_neg body))).
    { exact dnfree. }
    pose (dall := @ifo_context_generalize L H
      (ifo_goedel_gentzen_context Gamma) (ifo_neg body) dnfree').
    set (head := ifo_goedel_gentzen_formula (Semiformula_all phi)).
    set (tail := ifo_goedel_gentzen_context Gamma).
    assert (dhead : @ifo_context_derivation L H (head :: tail)
        (ifo_neg (IFOAll (ifo_neg body)))).
    { apply ifo_context_assumption. unfold head, tail, body,
        ifo_goedel_gentzen_formula. simpl. exact (GRLM_here _). }
    change (@ifo_context_derivation L H (head :: tail) IFOFalsum).
    exact (ifo_context_mdp dhead
      (ifo_context_weaken (fun p hp => GRLM_there head hp) dall)).
  - set (body := ifo_double_negation_translation (semiformula_neg phi)).
    set (instance := ifo_substitute (fun _ : Fin.t 1 => t) body).
    pose (ih0 := @ifo_goedel_gentzen L H D
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Gamma) d).
    assert (ehead :
        ifo_goedel_gentzen_formula
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi) = instance).
    { unfold instance, body, ifo_goedel_gentzen_formula,
        ifo_substitute, semiformula_substitute.
      rewrite ifo_rewrite_double_negation, semiformula_rewrite_neg.
      reflexivity. }
    assert (econtext :
        ifo_goedel_gentzen_context
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Gamma) =
        instance :: ifo_goedel_gentzen_context Gamma).
    { unfold ifo_goedel_gentzen_context. simpl. now rewrite ehead. }
    pose (ih := ifo_context_cast_context ih0 econtext).
    pose (dninstance := ifo_context_deduct ih).
    set (head := ifo_goedel_gentzen_formula (Semiformula_exists phi)).
    set (tail := ifo_goedel_gentzen_context Gamma).
    assert (dall : @ifo_context_derivation L H (head :: tail)
        (IFOAll body)).
    { apply ifo_context_assumption. unfold head, tail, body,
        ifo_goedel_gentzen_formula. simpl. exact (GRLM_here _). }
    pose (dinstance := ifo_context_specialize (phi := body) dall t).
    change (@ifo_context_derivation L H (head :: tail) IFOFalsum).
    exact (ifo_context_mdp
      (ifo_context_weaken (fun p hp => GRLM_there head hp) dninstance)
      dinstance).
Defined.

Theorem ifo_goedel_gentzen_provable : forall L
    (D : language_decidable_eq L) (H : ifo_hilbert L)
    (phi : proposition L),
  first_order_lk_provable phi ->
  inhabited
    (@ifo_hilbert_proof L H (ifo_double_negation_translation phi)).
Proof.
  intros L D H phi Hphi.
  apply (proj1 (@first_order_lk_provable_iff L phi)) in Hphi.
  destruct Hphi as [d].
  pose (dbot := @ifo_goedel_gentzen L H D [phi] d).
  pose (dneg := ifo_context_deduct dbot).
  pose (dneg0 := generic_empty_derivation_raw
    (ifo_hilbert_modus_ponens H) dneg).
  pose (Hm := ifo_hilbert_minimal_capability H).
  pose (eneg := @ifo_hilbert_neg_neg_double_negation L H phi).
  constructor.
  exact (IFOHPMdp (generic_minimal_iff_elim_left_raw Hm _ _ eneg) dneg0).
Qed.
