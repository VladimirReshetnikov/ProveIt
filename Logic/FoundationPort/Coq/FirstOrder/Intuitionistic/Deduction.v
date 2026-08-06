(** Type-valued Hilbert deduction for intuitionistic first-order logic. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Program.Equality Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus
  GenericEntailment GenericLogicSymbol GenericSemantics
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal
  PropositionalEntailmentInt.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record ifo_hilbert (L : language) : Type := {
  ifo_hilbert_axiom : ifo_proposition L -> Prop;
  ifo_hilbert_axiom_rewrite : forall phi,
    ifo_hilbert_axiom phi -> forall f : nat -> syntactic_term L,
    ifo_hilbert_axiom (ifo_rewrite (rew_rewrite f) phi)
}.

Definition ifo_hilbert_le {L} (H K : ifo_hilbert L) : Prop :=
  forall phi, ifo_hilbert_axiom H phi -> ifo_hilbert_axiom K phi.

Definition ifo_hilbert_minimal (L : language) : ifo_hilbert L.
Proof.
  refine {| ifo_hilbert_axiom := fun _ => False |}.
  intros phi H. contradiction.
Defined.

Inductive ifo_intuitionistic_axiom {L} : ifo_proposition L -> Prop :=
| IFOIntEFQ : forall phi, ifo_intuitionistic_axiom (IFOImp IFOFalsum phi).

Definition ifo_hilbert_intuitionistic (L : language) : ifo_hilbert L.
Proof.
  refine {| ifo_hilbert_axiom := ifo_intuitionistic_axiom |}.
  intros phi H f. destruct H as [phi]. simpl. constructor.
Defined.

Inductive ifo_classical_axiom {L} : ifo_proposition L -> Prop :=
| IFOClassicalEFQ : forall phi,
    ifo_classical_axiom (IFOImp IFOFalsum phi)
| IFOClassicalLEM : forall phi,
    ifo_classical_axiom (IFOOr phi (ifo_neg phi)).

Definition ifo_hilbert_classical (L : language) : ifo_hilbert L.
Proof.
  refine {| ifo_hilbert_axiom := ifo_classical_axiom |}.
  intros phi H f. destruct H as [phi | phi]; simpl; constructor.
Defined.

Lemma ifo_hilbert_minimal_le : forall L (H : ifo_hilbert L),
  ifo_hilbert_le (ifo_hilbert_minimal L) H.
Proof. intros L H phi Hphi. contradiction. Qed.

Lemma ifo_hilbert_intuitionistic_le_classical : forall L,
  ifo_hilbert_le (ifo_hilbert_intuitionistic L) (ifo_hilbert_classical L).
Proof. intros L phi H. destruct H. constructor. Qed.

Inductive ifo_hilbert_proof {L} (H : ifo_hilbert L) :
    ifo_proposition L -> Type :=
| IFOHPEaxm : forall phi, ifo_hilbert_axiom H phi -> ifo_hilbert_proof H phi
| IFOHPMdp : forall phi psi,
    ifo_hilbert_proof H (IFOImp phi psi) ->
    ifo_hilbert_proof H phi -> ifo_hilbert_proof H psi
| IFOHPGen : forall (phi : ifo_semiproposition L 1),
    ifo_hilbert_proof H (@ifo_free L 0 phi) ->
    ifo_hilbert_proof H (IFOAll phi)
| IFOHPVerum : ifo_hilbert_proof H ifo_verum
| IFOHPK : forall phi psi,
    ifo_hilbert_proof H (IFOImp phi (IFOImp psi phi))
| IFOHPS : forall phi psi chi,
    ifo_hilbert_proof H
      (IFOImp (IFOImp phi (IFOImp psi chi))
        (IFOImp (IFOImp phi psi) (IFOImp phi chi)))
| IFOHPAnd1 : forall phi psi,
    ifo_hilbert_proof H (IFOImp (IFOAnd phi psi) phi)
| IFOHPAnd2 : forall phi psi,
    ifo_hilbert_proof H (IFOImp (IFOAnd phi psi) psi)
| IFOHPAnd3 : forall phi psi,
    ifo_hilbert_proof H (IFOImp phi (IFOImp psi (IFOAnd phi psi)))
| IFOHPOr1 : forall phi psi,
    ifo_hilbert_proof H (IFOImp phi (IFOOr phi psi))
| IFOHPOr2 : forall phi psi,
    ifo_hilbert_proof H (IFOImp psi (IFOOr phi psi))
| IFOHPOr3 : forall phi psi chi,
    ifo_hilbert_proof H
      (IFOImp (IFOImp phi chi)
        (IFOImp (IFOImp psi chi) (IFOImp (IFOOr phi psi) chi)))
| IFOHPAll1 : forall (phi : ifo_semiproposition L 1) t,
    ifo_hilbert_proof H
      (IFOImp (IFOAll phi)
        (ifo_substitute (fun _ : Fin.t 1 => t) phi))
| IFOHPAll2 : forall (phi : ifo_proposition L)
    (psi : ifo_semiproposition L 1),
    ifo_hilbert_proof H
      (IFOImp (IFOAll (IFOImp (ifo_bshift phi) psi))
        (IFOImp phi (IFOAll psi)))
| IFOHPEx1 : forall t (phi : ifo_semiproposition L 1),
    ifo_hilbert_proof H
      (IFOImp (ifo_substitute (fun _ : Fin.t 1 => t) phi) (IFOExs phi))
| IFOHPEx2 : forall (phi : ifo_semiproposition L 1)
    (psi : ifo_proposition L),
    ifo_hilbert_proof H
      (IFOImp (IFOAll (IFOImp phi (ifo_bshift psi)))
        (IFOImp (IFOExs phi) psi)).

Arguments IFOHPEaxm {L H phi} _.
Arguments IFOHPMdp {L H phi psi} _ _.
Arguments IFOHPGen {L H phi} _.
Arguments IFOHPVerum {L H}.
Arguments IFOHPK {L H} _ _.
Arguments IFOHPS {L H} _ _ _.
Arguments IFOHPAnd1 {L H} _ _.
Arguments IFOHPAnd2 {L H} _ _.
Arguments IFOHPAnd3 {L H} _ _.
Arguments IFOHPOr1 {L H} _ _.
Arguments IFOHPOr2 {L H} _ _.
Arguments IFOHPOr3 {L H} _ _ _.
Arguments IFOHPAll1 {L H} _ _.
Arguments IFOHPAll2 {L H} _ _.
Arguments IFOHPEx1 {L H} _ _.
Arguments IFOHPEx2 {L H} _ _.

Definition ifo_hilbert_entailment (L : language) :
    generic_entailment (ifo_hilbert L) (ifo_proposition L) :=
  {| generic_proof := ifo_hilbert_proof |}.

Definition ifo_hilbert_proof_cast {L H phi psi}
    (d : @ifo_hilbert_proof L H phi) (e : phi = psi) :
    @ifo_hilbert_proof L H psi :=
  match e with eq_refl => d end.

Fixpoint ifo_hilbert_proof_depth {L H phi}
    (d : @ifo_hilbert_proof L H phi) : nat :=
  match d with
  | IFOHPMdp d1 d2 =>
      Nat.max (ifo_hilbert_proof_depth d1) (ifo_hilbert_proof_depth d2) + 1
  | IFOHPGen d => ifo_hilbert_proof_depth d + 1
  | _ => 0
  end.

Lemma ifo_hilbert_proof_depth_cast : forall (L : language) (H : ifo_hilbert L)
    (phi psi : ifo_proposition L)
    (d : @ifo_hilbert_proof L H phi) (e : phi = psi),
  ifo_hilbert_proof_depth (ifo_hilbert_proof_cast d e) =
  ifo_hilbert_proof_depth d.
Proof. intros L H phi psi d e. destruct e. reflexivity. Qed.

Definition ifo_hilbert_modus_ponens {L} (H : ifo_hilbert L) :
    generic_modus_ponens (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) H.
Proof.
  constructor. intros phi psi dpq dp. cbn in dpq, dp |- *.
  exact (IFOHPMdp dpq dp).
Defined.

Definition ifo_hilbert_identity {L H} (phi : ifo_proposition L) :
    @ifo_hilbert_proof L H (IFOImp phi phi) :=
  @generic_imp_identity_raw (ifo_hilbert L) (ifo_proposition L)
    (ifo_hilbert_entailment L) (ifo_connectives L nat 0) H
    (ifo_hilbert_modus_ponens H)
    (fun p q => IFOHPK p q) (fun p q r => IFOHPS p q r) phi.

Definition ifo_hilbert_neg_equiv {L H} (phi : ifo_proposition L) :
    @ifo_hilbert_proof L H
      (generic_axiom_neg_equiv (ifo_connectives L nat 0) phi).
Proof.
  unfold generic_axiom_neg_equiv, generic_formula_iff. cbn. unfold ifo_neg.
  exact (IFOHPMdp (IFOHPMdp (IFOHPAnd3 _ _)
    (ifo_hilbert_identity (IFOImp phi IFOFalsum)))
    (ifo_hilbert_identity (IFOImp phi IFOFalsum))).
Defined.

Definition ifo_hilbert_minimal_capability {L} (H : ifo_hilbert L) :
    generic_minimal_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) H.
Proof.
  constructor.
  - exact (ifo_hilbert_modus_ponens H).
  - exact (@ifo_hilbert_neg_equiv L H).
  - exact IFOHPVerum.
  - exact (fun p q => IFOHPK p q).
  - exact (fun p q r => IFOHPS p q r).
  - exact (fun p q => IFOHPAnd1 p q).
  - exact (fun p q => IFOHPAnd2 p q).
  - exact (fun p q => IFOHPAnd3 p q).
  - exact (fun p q => IFOHPOr1 p q).
  - exact (fun p q => IFOHPOr2 p q).
  - exact (fun p q r => IFOHPOr3 p q r).
Defined.

Definition ifo_context_derivation {L} (H : ifo_hilbert L)
    (Gamma : list (ifo_proposition L)) (phi : ifo_proposition L) : Type :=
  generic_list_derivation (ifo_hilbert_entailment L) H
    (ifo_connectives L nat 0) Gamma phi.

Definition ifo_context_assumption {L H Gamma phi}
    (h : generic_raw_list_member phi Gamma) :
    @ifo_context_derivation L H Gamma phi := GLD_assumption h.

Definition ifo_context_theorem {L H Gamma phi}
    (d : @ifo_hilbert_proof L H phi) :
    @ifo_context_derivation L H Gamma phi.
Proof.
  apply GLD_theorem. cbn. exact d.
Defined.

Definition ifo_context_cast {L H Gamma phi psi}
    (d : @ifo_context_derivation L H Gamma phi) (e : phi = psi) :
    @ifo_context_derivation L H Gamma psi :=
  match e with eq_refl => d end.

Definition ifo_context_mdp {L H Gamma phi psi}
    (dpq : @ifo_context_derivation L H Gamma (IFOImp phi psi))
    (dp : @ifo_context_derivation L H Gamma phi) :
    @ifo_context_derivation L H Gamma psi.
Proof.
  change (generic_list_derivation (ifo_hilbert_entailment L) H
    (ifo_connectives L nat 0) Gamma
    (generic_imp (ifo_connectives L nat 0) phi psi)) in dpq.
  exact (GLD_mdp dpq dp).
Defined.

Definition ifo_context_weaken {L H Gamma Delta phi}
    (incl : forall p, generic_raw_list_member p Gamma ->
      generic_raw_list_member p Delta)
    (d : @ifo_context_derivation L H Gamma phi) :
    @ifo_context_derivation L H Delta phi :=
  generic_list_derivation_weaken_raw incl d.

Definition ifo_context_deduct {L H Gamma phi psi}
    (d : @ifo_context_derivation L H (phi :: Gamma) psi) :
    @ifo_context_derivation L H Gamma (IFOImp phi psi) :=
  generic_minimal_list_deduction_raw (ifo_hilbert_minimal_capability H) d.

Definition ifo_context_deduct_inverse {L H Gamma phi psi}
    (d : @ifo_context_derivation L H Gamma (IFOImp phi psi)) :
    @ifo_context_derivation L H (phi :: Gamma) psi :=
  generic_list_deduction_inverse_raw d.

(** Universal elimination does not need any structural hypothesis on the
    Hilbert axiom set. *)
Definition ifo_hilbert_specialize {L H} (phi : ifo_semiproposition L 1)
    (d : @ifo_hilbert_proof L H (IFOAll phi)) (t : syntactic_term L) :
    @ifo_hilbert_proof L H
      (ifo_substitute (fun _ : Fin.t 1 => t) phi) :=
  IFOHPMdp (IFOHPAll1 phi t) d.

(** Generalization with one closed antecedent.  The rewrite equality which
    expresses the eigenvariable side condition is factored in [Rew]. *)
Definition ifo_hilbert_imply_all {L H} (phi : ifo_proposition L)
    (psi : ifo_semiproposition L 1)
    (d : @ifo_hilbert_proof L H
      (IFOImp (ifo_shift phi) (@ifo_free L 0 psi))) :
    @ifo_hilbert_proof L H (IFOImp phi (IFOAll psi)).
Proof.
  apply (IFOHPMdp (IFOHPAll2 phi psi)).
  apply IFOHPGen.
  refine (ifo_hilbert_proof_cast d _).
  symmetry. apply ifo_free_imp_bshift.
Defined.

(** Foundation derives finite-context generalization through a conjunction
    encoding.  Structural recursion over positional list contexts is both
    stronger and constructive: duplicates are retained and no formula
    equality decision is required. *)
Fixpoint ifo_context_generalize {L H Gamma} (phi : ifo_semiproposition L 1)
    (d : @ifo_context_derivation L H (map ifo_shift Gamma)
      (@ifo_free L 0 phi)) {struct Gamma} :
    @ifo_context_derivation L H Gamma (IFOAll phi).
Proof.
  destruct Gamma as [|a Gamma].
  - simpl in d. apply ifo_context_theorem. apply IFOHPGen.
    exact (generic_empty_derivation_raw (ifo_hilbert_modus_ponens H) d).
  - simpl in d.
    pose (dimp := ifo_context_deduct d).
    pose (dbody := ifo_context_cast dimp
      (eq_sym (ifo_free_imp_bshift (L := L) a phi))).
    pose (dall := @ifo_context_generalize L H Gamma
      (IFOImp (ifo_bshift a) phi) dbody).
    apply (ifo_context_mdp
      (ifo_context_mdp
        (ifo_context_theorem (Gamma := a :: Gamma) (IFOHPAll2 a phi))
        (ifo_context_weaken
          (fun p hp => GRLM_there a hp) dall))
      (ifo_context_assumption (GRLM_here Gamma))).
Defined.

Definition ifo_context_specialize {L H Gamma}
    (phi : ifo_semiproposition L 1)
    (d : @ifo_context_derivation L H Gamma (IFOAll phi))
    (t : syntactic_term L) :
    @ifo_context_derivation L H Gamma
      (ifo_substitute (fun _ : Fin.t 1 => t) phi) :=
  ifo_context_mdp
    (ifo_context_theorem (Gamma := Gamma) (IFOHPAll1 phi t)) d.

(** Universal implication is functorial.  The proof uses the stronger direct
    list-context generalization above, so it avoids Foundation's decidable
    equality requirement for conjunction-encoded finite contexts. *)
Definition ifo_hilbert_all_imply_all_of_all_imply {L H}
    (phi psi : ifo_semiproposition L 1) :
    @ifo_hilbert_proof L H
      (IFOImp (IFOAll (IFOImp phi psi))
        (IFOImp (IFOAll phi) (IFOAll psi))).
Proof.
  set (Gamma := [IFOAll phi; IFOAll (IFOImp phi psi)]).
  assert (dallphi : @ifo_context_derivation L H (map ifo_shift Gamma)
      (ifo_shift (IFOAll phi))).
  { apply ifo_context_assumption. unfold Gamma. simpl.
    exact (GRLM_here _). }
  assert (dallimp : @ifo_context_derivation L H (map ifo_shift Gamma)
      (ifo_shift (IFOAll (IFOImp phi psi)))).
  { apply ifo_context_assumption. unfold Gamma. simpl.
    exact (GRLM_there _ (GRLM_here _)). }
  pose (dphi0 := ifo_context_specialize (phi := ifo_shift phi)
    (ifo_context_cast dallphi (ifo_shift_all (L := L) phi))
    (Semiterm_fvar 0)).
  pose (dimp0 := ifo_context_specialize
    (phi := ifo_shift (IFOImp phi psi))
    (ifo_context_cast dallimp (ifo_shift_all (L := L) (IFOImp phi psi)))
    (Semiterm_fvar 0)).
  pose (dphi := ifo_context_cast dphi0
    (ifo_substitute_shift_one_eq_free (L := L) phi)).
  pose (dimp := ifo_context_cast dimp0
    (ifo_substitute_shift_one_eq_free (L := L) (IFOImp phi psi))).
  pose (dpsi := ifo_context_mdp dimp dphi).
  pose (dallpsi := @ifo_context_generalize L H Gamma psi dpsi).
  unfold Gamma in dallpsi.
  exact (generic_empty_derivation_raw (ifo_hilbert_modus_ponens H)
    (ifo_context_deduct (ifo_context_deduct dallpsi))).
Defined.

Definition ifo_hilbert_all_iff_all_of_free_iff {L H}
    (phi psi : ifo_semiproposition L 1)
    (d : @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (@ifo_free L 0 phi) (@ifo_free L 0 psi))
        (IFOImp (@ifo_free L 0 psi) (@ifo_free L 0 phi)))) :
    @ifo_hilbert_proof L H
      (IFOAnd
        (IFOImp (IFOAll phi) (IFOAll psi))
        (IFOImp (IFOAll psi) (IFOAll phi))).
Proof.
  pose (Hm := ifo_hilbert_minimal_capability H).
  pose (dfwd := generic_minimal_iff_elim_left_raw Hm
    (@ifo_free L 0 phi) (@ifo_free L 0 psi) d).
  pose (drev := generic_minimal_iff_elim_right_raw Hm
    (@ifo_free L 0 phi) (@ifo_free L 0 psi) d).
  pose (dallfwd := IFOHPGen (phi := IFOImp phi psi) dfwd).
  pose (dallrev := IFOHPGen (phi := IFOImp psi phi) drev).
  apply (generic_minimal_iff_intro_raw Hm (IFOAll phi) (IFOAll psi)).
  - exact (IFOHPMdp
      (ifo_hilbert_all_imply_all_of_all_imply phi psi) dallfwd).
  - exact (IFOHPMdp
      (ifo_hilbert_all_imply_all_of_all_imply psi phi) dallrev).
Defined.

(** Double-negation elimination is stable under every capture-avoiding
    rewrite of a weak-negative formula into the proposition fragment.  This
    strengthens the source theorem, removes its decidable-equality premise,
    and makes termination structural on the negativity witness. *)
Fixpoint ifo_hilbert_dne_negative_rewrite {L H X n}
    (phi : ifo_semiformula L X n) {struct phi} :
    ifo_negative n phi -> forall w : rew L X n nat 0,
    @ifo_hilbert_proof L H
      (IFOImp (ifo_neg (ifo_neg (ifo_rewrite w phi)))
        (ifo_rewrite w phi)).
Proof.
  destruct phi as [n | n k R v | n phi psi | n phi psi |
    n phi psi | n phi | n phi]; intros h w.
  - simpl. exact (generic_minimal_double_neg_bottom_elim_raw
      (ifo_hilbert_minimal_capability H)).
  - exact (False_rect _ (ifo_negative_not_rel h)).
  - simpl. pose (Hm := ifo_hilbert_minimal_capability H).
    pose (dleftnn := generic_minimal_double_neg_map_raw Hm
      (IFOAnd (ifo_rewrite w phi) (ifo_rewrite w psi))
      (ifo_rewrite w phi)
      (IFOHPAnd1 (ifo_rewrite w phi) (ifo_rewrite w psi))).
    pose (drightnn := generic_minimal_double_neg_map_raw Hm
      (IFOAnd (ifo_rewrite w phi) (ifo_rewrite w psi))
      (ifo_rewrite w psi)
      (IFOHPAnd2 (ifo_rewrite w phi) (ifo_rewrite w psi))).
    apply (generic_minimal_right_and_intro_raw Hm
      (ifo_neg (ifo_neg
        (IFOAnd (ifo_rewrite w phi) (ifo_rewrite w psi))))
      (ifo_rewrite w phi) (ifo_rewrite w psi)).
    + exact (generic_minimal_imp_trans_raw Hm _ _ _ dleftnn
        (@ifo_hilbert_dne_negative_rewrite L H X n phi
          (proj1 (proj1 (ifo_negative_and_iff phi psi) h)) w)).
    + exact (generic_minimal_imp_trans_raw Hm _ _ _ drightnn
        (@ifo_hilbert_dne_negative_rewrite L H X n psi
          (proj2 (proj1 (ifo_negative_and_iff phi psi) h)) w)).
  - exact (False_rect _ (ifo_negative_not_or h)).
  - simpl. pose (Hm := ifo_hilbert_minimal_capability H).
    pose (ddist := generic_minimal_double_neg_imp_distribution_raw Hm
      (ifo_rewrite w phi) (ifo_rewrite w psi)).
    pose (dpre := generic_minimal_imp_lift_left_raw Hm
      (ifo_neg (ifo_neg (ifo_rewrite w phi))) (ifo_rewrite w phi)
      (ifo_neg (ifo_neg (ifo_rewrite w psi)))
      (generic_minimal_dni_raw Hm (ifo_rewrite w phi))).
    pose (dpost := generic_minimal_imp_lift_right_raw Hm
      (ifo_neg (ifo_neg (ifo_rewrite w psi))) (ifo_rewrite w psi)
      (ifo_rewrite w phi)
      (@ifo_hilbert_dne_negative_rewrite L H X n psi
        (proj1 (ifo_negative_imp_iff phi psi) h) w)).
    exact (generic_minimal_imp_trans_raw Hm _ _ _ ddist
      (generic_minimal_imp_trans_raw Hm _ _ _ dpre dpost)).
  - simpl. pose (Hm := ifo_hilbert_minimal_capability H).
    set (body := ifo_rewrite (rew_q w) phi).
    set (a := IFOAll body).
    set (Gamma := [ifo_neg (ifo_neg a)]).
    pose (ihfree := @ifo_hilbert_dne_negative_rewrite L H X (S n) phi
      (proj1 (ifo_negative_all_iff phi) h)
      (rew_comp (@rew_free L 0) (rew_q w))).
    rewrite ifo_rewrite_comp in ihfree.
    assert (dnnall : @ifo_context_derivation L H (map ifo_shift Gamma)
        (ifo_neg (ifo_neg (IFOAll (ifo_shift body))))).
    { refine (@ifo_context_cast L H (map ifo_shift Gamma)
        (ifo_shift (ifo_neg (ifo_neg a)))
        (ifo_neg (ifo_neg (IFOAll (ifo_shift body)))) _ _).
      - apply ifo_context_assumption. unfold Gamma. simpl.
        exact (GRLM_here _).
      - unfold a. apply ifo_shift_double_neg_all. }
    assert (dnfree : @ifo_context_derivation L H
        (ifo_neg (@ifo_free L 0 body) :: map ifo_shift Gamma)
        (ifo_neg (@ifo_free L 0 body))).
    { apply ifo_context_assumption. exact (GRLM_here _). }
    assert (dallshift : @ifo_context_derivation L H
        (IFOAll (ifo_shift body) ::
          ifo_neg (@ifo_free L 0 body) :: map ifo_shift Gamma)
        (IFOAll (ifo_shift body))).
    { apply ifo_context_assumption. exact (GRLM_here _). }
    pose (dfree0 := ifo_context_specialize (phi := ifo_shift body)
      dallshift (Semiterm_fvar 0)).
    pose (dfree := ifo_context_cast dfree0
      (ifo_substitute_shift_one_eq_free (L := L) body)).
    pose (dbot0 := ifo_context_mdp
      (ifo_context_weaken
        (fun p hp => GRLM_there (IFOAll (ifo_shift body)) hp) dnfree)
      dfree).
    pose (dnegall := ifo_context_deduct dbot0).
    pose (dbot1 := ifo_context_mdp
      (ifo_context_weaken
        (fun p hp => GRLM_there (ifo_neg (@ifo_free L 0 body)) hp)
        dnnall) dnegall).
    pose (dnnfree := ifo_context_deduct dbot1).
    pose (dfree_final := ifo_context_mdp
      (ifo_context_theorem (Gamma := map ifo_shift Gamma) ihfree) dnnfree).
    pose (dall := @ifo_context_generalize L H Gamma body dfree_final).
    unfold Gamma, a in dall.
    exact (generic_empty_derivation_raw (ifo_hilbert_modus_ponens H)
      (ifo_context_deduct dall)).
  - exact (False_rect _ (ifo_negative_not_exs h)).
Defined.

Definition ifo_hilbert_dne_negative {L H} (phi : ifo_proposition L)
    (h : ifo_negative 0 phi) :
    @ifo_hilbert_proof L H (IFOImp (ifo_neg (ifo_neg phi)) phi).
Proof.
  refine (ifo_hilbert_proof_cast
    (@ifo_hilbert_dne_negative_rewrite L H nat 0 phi h rew_id) _).
  now rewrite ifo_rewrite_id.
Defined.

Definition ifo_context_of_double_neg_negative {L H Gamma}
    (phi : ifo_proposition L)
    (d : @ifo_context_derivation L H Gamma (ifo_neg (ifo_neg phi)))
    (h : ifo_negative 0 phi) :
    @ifo_context_derivation L H Gamma phi :=
  ifo_context_mdp
    (ifo_context_theorem (Gamma := Gamma)
      (@ifo_hilbert_dne_negative L H phi h)) d.

Definition ifo_hilbert_double_neg_iff_negative {L H}
    (phi : ifo_proposition L) (h : ifo_negative 0 phi) :
    @ifo_hilbert_proof L H
      (IFOAnd (IFOImp (ifo_neg (ifo_neg phi)) phi)
        (IFOImp phi (ifo_neg (ifo_neg phi)))) :=
  generic_minimal_iff_intro_raw (ifo_hilbert_minimal_capability H)
    (ifo_neg (ifo_neg phi)) phi
    (@ifo_hilbert_dne_negative L H phi h)
    (generic_minimal_dni_raw (ifo_hilbert_minimal_capability H) phi).

(** The weak-negative fragment also admits ex falso in every Hilbert system,
    even the minimal one.  As for DNE, the rewrite-parametric statement is
    structurally recursive and strictly more general than the source result. *)
Fixpoint ifo_hilbert_efq_negative_rewrite {L H X n}
    (phi : ifo_semiformula L X n) {struct phi} :
    ifo_negative n phi -> forall w : rew L X n nat 0,
    @ifo_hilbert_proof L H (IFOImp IFOFalsum (ifo_rewrite w phi)).
Proof.
  destruct phi as [n | n k R v | n phi psi | n phi psi |
    n phi psi | n phi | n phi]; intros h w.
  - simpl. exact (ifo_hilbert_identity IFOFalsum).
  - exact (False_rect _ (ifo_negative_not_rel h)).
  - simpl. apply (generic_minimal_right_and_intro_raw
      (ifo_hilbert_minimal_capability H) IFOFalsum
      (ifo_rewrite w phi) (ifo_rewrite w psi)).
    + exact (@ifo_hilbert_efq_negative_rewrite L H X n phi
        (proj1 (proj1 (ifo_negative_and_iff phi psi) h)) w).
    + exact (@ifo_hilbert_efq_negative_rewrite L H X n psi
        (proj2 (proj1 (ifo_negative_and_iff phi psi) h)) w).
  - exact (False_rect _ (ifo_negative_not_or h)).
  - simpl. exact (generic_minimal_imp_trans_raw
      (ifo_hilbert_minimal_capability H)
      IFOFalsum (ifo_rewrite w psi)
      (IFOImp (ifo_rewrite w phi) (ifo_rewrite w psi))
      (@ifo_hilbert_efq_negative_rewrite L H X n psi
        (proj1 (ifo_negative_imp_iff phi psi) h) w)
      (IFOHPK (ifo_rewrite w psi) (ifo_rewrite w phi))).
  - simpl. set (body := ifo_rewrite (rew_q w) phi).
    pose (ihfree := @ifo_hilbert_efq_negative_rewrite L H X (S n) phi
      (proj1 (ifo_negative_all_iff phi) h)
      (rew_comp (@rew_free L 0) (rew_q w))).
    rewrite ifo_rewrite_comp in ihfree.
    exact (@ifo_hilbert_imply_all L H IFOFalsum body ihfree).
  - exact (False_rect _ (ifo_negative_not_exs h)).
Defined.

Definition ifo_hilbert_efq_negative {L H} (phi : ifo_proposition L)
    (h : ifo_negative 0 phi) :
    @ifo_hilbert_proof L H (IFOImp IFOFalsum phi).
Proof.
  refine (ifo_hilbert_proof_cast
    (@ifo_hilbert_efq_negative_rewrite L H nat 0 phi h rew_id) _).
  now rewrite ifo_rewrite_id.
Defined.

Definition ifo_hilbert_iff_neg_of_neg_iff {L H}
    (phi psi : ifo_proposition L) (h : ifo_negative 0 phi)
    (d : @ifo_hilbert_proof L H
      (IFOAnd (IFOImp (ifo_neg phi) psi)
        (IFOImp psi (ifo_neg phi)))) :
    @ifo_hilbert_proof L H
      (IFOAnd (IFOImp phi (ifo_neg psi))
        (IFOImp (ifo_neg psi) phi)).
Proof.
  pose (Hm := ifo_hilbert_minimal_capability H).
  exact (generic_minimal_iff_trans_raw Hm phi
    (ifo_neg (ifo_neg phi)) (ifo_neg psi)
    (generic_minimal_iff_symm_raw Hm
      (ifo_neg (ifo_neg phi)) phi
      (@ifo_hilbert_double_neg_iff_negative L H phi h))
    (generic_minimal_neg_iff_congr_raw Hm (ifo_neg phi) psi d)).
Defined.

(** Simultaneously rewrite every free variable in a Hilbert derivation. *)
Fixpoint ifo_hilbert_proof_rewrite {L H phi}
    (f : nat -> syntactic_term L) (d : @ifo_hilbert_proof L H phi)
    {struct d} :
    @ifo_hilbert_proof L H (ifo_rewrite (rew_rewrite f) phi).
Proof.
  destruct d as
    [phi hphi
    | phi psi dpq dp
    | phi d
    |
    | phi psi
    | phi psi chi
    | phi psi
    | phi psi
    | phi psi
    | phi psi
    | phi psi
    | phi psi chi
    | phi t
    | phi psi
    | t phi
    | phi psi].
  - exact (IFOHPEaxm (@ifo_hilbert_axiom_rewrite L H phi hphi f)).
  - simpl. exact (IFOHPMdp
      (@ifo_hilbert_proof_rewrite L H (IFOImp phi psi) f dpq)
      (@ifo_hilbert_proof_rewrite L H phi f dp)).
  - simpl. apply IFOHPGen.
    refine (ifo_hilbert_proof_cast
      (@ifo_hilbert_proof_rewrite L H (@ifo_free L 0 phi)
        (rew_rewrite_under_free f) d) _).
    apply ifo_rewrite_under_free_free.
  - simpl. exact IFOHPVerum.
  - simpl. exact (IFOHPK (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPS (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)
      (ifo_rewrite (rew_rewrite f) chi)).
  - simpl. exact (IFOHPAnd1 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPAnd2 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPAnd3 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPOr1 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPOr2 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)).
  - simpl. exact (IFOHPOr3 (ifo_rewrite (rew_rewrite f) phi)
      (ifo_rewrite (rew_rewrite f) psi)
      (ifo_rewrite (rew_rewrite f) chi)).
  - refine (ifo_hilbert_proof_cast
      (IFOHPAll1 (ifo_rewrite (rew_q (rew_rewrite f)) phi)
        (rew_apply (rew_rewrite f) t)) _).
    symmetry. apply ifo_rewrite_all1_shape.
  - refine (ifo_hilbert_proof_cast
      (IFOHPAll2 (ifo_rewrite (rew_rewrite f) phi)
        (ifo_rewrite (rew_q (rew_rewrite f)) psi)) _).
    symmetry. apply ifo_rewrite_all2_shape.
  - refine (ifo_hilbert_proof_cast
      (IFOHPEx1 (rew_apply (rew_rewrite f) t)
        (ifo_rewrite (rew_q (rew_rewrite f)) phi)) _).
    symmetry. apply ifo_rewrite_ex1_shape.
  - refine (ifo_hilbert_proof_cast
      (IFOHPEx2 (ifo_rewrite (rew_q (rew_rewrite f)) phi)
        (ifo_rewrite (rew_rewrite f) psi)) _).
    symmetry. apply ifo_rewrite_ex2_shape.
Defined.

Lemma ifo_hilbert_proof_depth_rewrite : forall L H phi
    (d : @ifo_hilbert_proof L H phi) f,
  ifo_hilbert_proof_depth (ifo_hilbert_proof_rewrite f d) =
  ifo_hilbert_proof_depth d.
Proof.
  intros L H phi d. induction d; intro f; cbn;
    try rewrite ifo_hilbert_proof_depth_cast; try reflexivity.
  all: try (now rewrite (IHd1 f), (IHd2 f)).
  all: try (now rewrite ifo_hilbert_proof_depth_cast,
      (IHd (rew_rewrite_under_free f))).
  all: try (now rewrite (IHd (rew_rewrite_under_free f))).
  f_equal. apply f_equal2; [exact (IHd1 f) | exact (IHd2 f)].
Qed.

Fixpoint ifo_hilbert_proof_weaken {L H K phi}
    (h : ifo_hilbert_le H K) (d : @ifo_hilbert_proof L H phi) :
    @ifo_hilbert_proof L K phi :=
  match d with
  | IFOHPEaxm hp => IFOHPEaxm (h _ hp)
  | IFOHPMdp d1 d2 =>
      IFOHPMdp (ifo_hilbert_proof_weaken h d1)
        (ifo_hilbert_proof_weaken h d2)
  | IFOHPGen d => IFOHPGen (ifo_hilbert_proof_weaken h d)
  | IFOHPVerum => IFOHPVerum
  | IFOHPK p q => IFOHPK p q
  | IFOHPS p q r => IFOHPS p q r
  | IFOHPAnd1 p q => IFOHPAnd1 p q
  | IFOHPAnd2 p q => IFOHPAnd2 p q
  | IFOHPAnd3 p q => IFOHPAnd3 p q
  | IFOHPOr1 p q => IFOHPOr1 p q
  | IFOHPOr2 p q => IFOHPOr2 p q
  | IFOHPOr3 p q r => IFOHPOr3 p q r
  | IFOHPAll1 p t => IFOHPAll1 p t
  | IFOHPAll2 p q => IFOHPAll2 p q
  | IFOHPEx1 t p => IFOHPEx1 t p
  | IFOHPEx2 p q => IFOHPEx2 p q
  end.

(** * Sentence theories *)

Definition ifo_empty_elim (x : Empty_set) : False := match x with end.

Definition ifo_sentence_embed {L} (phi : ifo_sentence L) :
    ifo_proposition L :=
  @ifo_emb L Empty_set nat 0 ifo_empty_elim phi.

Lemma ifo_sentence_embed_imp : forall L (phi psi : ifo_sentence L),
  ifo_sentence_embed (IFOImp phi psi) =
  IFOImp (ifo_sentence_embed phi) (ifo_sentence_embed psi).
Proof. reflexivity. Qed.

(** A Type-valued axiom family includes Foundation's Prop-valued sets as a
    special case and preserves assumption witnesses constructively. *)
Record ifo_theory (L : language) : Type := {
  ifo_theory_axiom : ifo_sentence L -> Type
}.

Definition ifo_theory_le {L} (T U : ifo_theory L) : Type :=
  forall phi, ifo_theory_axiom T phi -> ifo_theory_axiom U phi.

Definition ifo_theory_empty {L} : ifo_theory L :=
  {| ifo_theory_axiom := fun _ => Empty_set |}.

Inductive ifo_theory_adjoin_axiom {L}
    (phi : ifo_sentence L) (T : ifo_theory L) :
    ifo_sentence L -> Type :=
| IFOTheoryAdjoinHere : ifo_theory_adjoin_axiom phi T phi
| IFOTheoryAdjoinThere : forall psi, ifo_theory_axiom T psi ->
    ifo_theory_adjoin_axiom phi T psi.

Arguments IFOTheoryAdjoinHere {L phi T}.
Arguments IFOTheoryAdjoinThere {L phi T psi} _.

Definition ifo_theory_adjoin {L} (phi : ifo_sentence L)
    (T : ifo_theory L) : ifo_theory L :=
  {| ifo_theory_axiom := ifo_theory_adjoin_axiom phi T |}.

(** Proof-relevant image of a sentence theory under embedding. *)
Definition ifo_theory_formula_context {L} (T : ifo_theory L)
    (p : ifo_proposition L) : Type :=
  { phi : ifo_sentence L &
    (ifo_theory_axiom T phi * (ifo_sentence_embed phi = p))%type }.

Definition ifo_theory_proof {L H} (T : ifo_theory L)
    (phi : ifo_sentence L) : Type :=
  generic_type_context_derivation (ifo_hilbert_entailment L) H
    (ifo_connectives L nat 0) (ifo_theory_formula_context T)
    (ifo_sentence_embed phi).

Definition ifo_theory_entailment (L : language) (H : ifo_hilbert L) :
    generic_entailment (ifo_theory L) (ifo_sentence L) :=
  {| generic_proof := @ifo_theory_proof L H |}.

Definition ifo_theory_proof_cast {L H T phi psi}
    (d : @ifo_theory_proof L H T phi) (e : phi = psi) :
    @ifo_theory_proof L H T psi :=
  match e with eq_refl => d end.

Definition ifo_theory_proof_weaken {L H T U phi}
    (incl : ifo_theory_le T U) (d : @ifo_theory_proof L H T phi) :
    @ifo_theory_proof L H U phi.
Proof.
  refine (generic_type_context_derivation_weaken_raw _ d).
  intros p [psi [hpsi e]]. exists psi. split; [exact (incl psi hpsi) | exact e].
Defined.

Definition ifo_theory_assumption {L H T phi}
    (h : ifo_theory_axiom T phi) : @ifo_theory_proof L H T phi :=
  GTCD_assumption (existT _ phi (h, eq_refl)).

Definition ifo_theory_of_hilbert {L H T phi}
    (d : @ifo_hilbert_proof L H (ifo_sentence_embed phi)) :
    @ifo_theory_proof L H T phi.
Proof. apply GTCD_theorem. cbn. exact d. Defined.

Definition ifo_theory_adjoin_context_forward {L T phi p}
    (h : @ifo_theory_formula_context L (ifo_theory_adjoin phi T) p) :
    generic_type_context_adjoin (ifo_sentence_embed phi)
      (ifo_theory_formula_context T) p.
Proof.
  destruct h as [psi [hpsi e]].
  change (ifo_theory_adjoin_axiom phi T psi) in hpsi.
  dependent destruction hpsi.
  - destruct e. exact GTCA_here.
  - apply GTCA_there. exists psi. now split.
Defined.

Definition ifo_theory_adjoin_context_backward {L T phi p}
    (h : generic_type_context_adjoin (ifo_sentence_embed phi)
      (ifo_theory_formula_context T) p) :
    @ifo_theory_formula_context L (ifo_theory_adjoin phi T) p.
Proof.
  destruct h as [|p hp].
  - exists phi. split; [exact IFOTheoryAdjoinHere | reflexivity].
  - destruct hp as [psi [hpsi e]]. exists psi.
    split; [exact (IFOTheoryAdjoinThere hpsi) | exact e].
Defined.

Definition ifo_theory_deduct {L H T phi psi}
    (d : @ifo_theory_proof L H (ifo_theory_adjoin phi T) psi) :
    @ifo_theory_proof L H T (IFOImp phi psi).
Proof.
  change (generic_type_context_derivation (ifo_hilbert_entailment L) H
    (ifo_connectives L nat 0) (ifo_theory_formula_context T)
    (IFOImp (ifo_sentence_embed phi) (ifo_sentence_embed psi))).
  apply (generic_minimal_type_context_deduction_raw
    (ifo_hilbert_minimal_capability H)).
  exact (generic_type_context_derivation_weaken_raw
    (fun p hp => ifo_theory_adjoin_context_forward hp) d).
Defined.

Definition ifo_theory_deduct_inverse {L H T phi psi}
    (d : @ifo_theory_proof L H T (IFOImp phi psi)) :
    @ifo_theory_proof L H (ifo_theory_adjoin phi T) psi.
Proof.
  change (generic_type_context_derivation (ifo_hilbert_entailment L) H
    (ifo_connectives L nat 0) (ifo_theory_formula_context T)
    (IFOImp (ifo_sentence_embed phi) (ifo_sentence_embed psi))) in d.
  pose (d' := generic_type_context_deduction_inverse_raw d).
  exact (generic_type_context_derivation_weaken_raw
    (fun p hp => ifo_theory_adjoin_context_backward hp) d').
Defined.

Definition ifo_theory_modus_ponens {L H} (T : ifo_theory L) :
    generic_modus_ponens (@ifo_theory_entailment L H)
      (ifo_connectives L Empty_set 0) T.
Proof.
  constructor. intros phi psi dpq dp. cbn in dpq, dp |- *.
  exact (GTCD_mdp dpq dp).
Defined.

Definition ifo_theory_minimal_capability {L H} (T : ifo_theory L) :
    generic_minimal_entailment (@ifo_theory_entailment L H)
      (ifo_connectives L Empty_set 0) T.
Proof.
  constructor.
  - exact (ifo_theory_modus_ponens T).
  - intro phi. apply ifo_theory_of_hilbert.
    exact (ifo_hilbert_neg_equiv (ifo_sentence_embed phi)).
  - apply ifo_theory_of_hilbert. exact IFOHPVerum.
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPK (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi chi. apply ifo_theory_of_hilbert.
    exact (IFOHPS (ifo_sentence_embed phi) (ifo_sentence_embed psi)
      (ifo_sentence_embed chi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPAnd1 (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPAnd2 (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPAnd3 (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPOr1 (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (IFOHPOr2 (ifo_sentence_embed phi) (ifo_sentence_embed psi)).
  - intros phi psi chi. apply ifo_theory_of_hilbert.
    exact (IFOHPOr3 (ifo_sentence_embed phi) (ifo_sentence_embed psi)
      (ifo_sentence_embed chi)).
Defined.

Definition ifo_hilbert_intuitionistic_capability {L} (H : ifo_hilbert L)
    (efq : forall phi : ifo_proposition L,
      @ifo_hilbert_proof L H (IFOImp IFOFalsum phi)) :
    generic_intuitionistic_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) H.
Proof.
  constructor.
  - exact (ifo_hilbert_minimal_capability H).
  - constructor. exact efq.
Defined.

Definition ifo_hilbert_intuitionistic_system_capability (L : language) :
    generic_intuitionistic_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) (ifo_hilbert_intuitionistic L) :=
  @ifo_hilbert_intuitionistic_capability L (ifo_hilbert_intuitionistic L)
    (fun phi => @IFOHPEaxm L (ifo_hilbert_intuitionistic L)
      (IFOImp IFOFalsum phi) (IFOIntEFQ phi)).

Definition ifo_theory_intuitionistic_capability {L H}
    (T : ifo_theory L)
    (Hi : generic_intuitionistic_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) H) :
    generic_intuitionistic_entailment (@ifo_theory_entailment L H)
      (ifo_connectives L Empty_set 0) T.
Proof.
  constructor.
  - exact (ifo_theory_minimal_capability T).
  - constructor. intro phi. apply ifo_theory_of_hilbert.
    exact (generic_efq_raw (generic_intuitionistic_has_efq Hi)
      (ifo_sentence_embed phi)).
Defined.

Definition ifo_theory_classical_capability {L H}
    (T : ifo_theory L)
    (Hc : generic_classical_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) H) :
    generic_classical_entailment (@ifo_theory_entailment L H)
      (ifo_connectives L Empty_set 0) T.
Proof.
  constructor.
  - exact (ifo_theory_modus_ponens T).
  - intro phi. apply ifo_theory_of_hilbert.
    exact (generic_classical_neg_equiv Hc (ifo_sentence_embed phi)).
  - apply ifo_theory_of_hilbert. exact (generic_classical_verum Hc).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_K Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi chi. apply ifo_theory_of_hilbert.
    exact (generic_classical_S Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi) (ifo_sentence_embed chi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_and1 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_and2 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_and3 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_or1 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi. apply ifo_theory_of_hilbert.
    exact (generic_classical_or2 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi)).
  - intros phi psi chi. apply ifo_theory_of_hilbert.
    exact (generic_classical_or3 Hc (ifo_sentence_embed phi)
      (ifo_sentence_embed psi) (ifo_sentence_embed chi)).
  - intro phi. apply ifo_theory_of_hilbert.
    exact (generic_classical_dne Hc (ifo_sentence_embed phi)).
Defined.

Definition ifo_hilbert_classical_lem_capability (L : language) :
    generic_has_axiom_lem (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) (ifo_hilbert_classical L).
Proof.
  constructor. intro phi.
  exact (@IFOHPEaxm L (ifo_hilbert_classical L)
    (IFOOr phi (ifo_neg phi)) (IFOClassicalLEM phi)).
Defined.

Definition ifo_hilbert_classical_efq_capability (L : language) :
    generic_has_axiom_efq (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) (ifo_hilbert_classical L).
Proof.
  constructor. intro phi.
  exact (@IFOHPEaxm L (ifo_hilbert_classical L)
    (IFOImp IFOFalsum phi) (IFOClassicalEFQ phi)).
Defined.

Definition ifo_hilbert_classical_system_capability (L : language) :
    generic_classical_entailment (ifo_hilbert_entailment L)
      (ifo_connectives L nat 0) (ifo_hilbert_classical L).
Proof.
  pose (H := ifo_hilbert_classical L).
  pose (Hm := ifo_hilbert_minimal_capability H).
  constructor.
  - exact (ifo_hilbert_modus_ponens H).
  - exact (@ifo_hilbert_neg_equiv L H).
  - exact IFOHPVerum.
  - exact (fun p q => IFOHPK p q).
  - exact (fun p q r => IFOHPS p q r).
  - exact (fun p q => IFOHPAnd1 p q).
  - exact (fun p q => IFOHPAnd2 p q).
  - exact (fun p q => IFOHPAnd3 p q).
  - exact (fun p q => IFOHPOr1 p q).
  - exact (fun p q => IFOHPOr2 p q).
  - exact (fun p q r => IFOHPOr3 p q r).
  - intro p. exact (generic_dne_of_lem_efq_raw
      (ifo_hilbert_modus_ponens H)
      (fun q r => IFOHPK q r)
      (fun q r s => IFOHPS q r s)
      (fun q r s => IFOHPOr3 q r s)
      (ifo_hilbert_classical_lem_capability L)
      (ifo_hilbert_classical_efq_capability L)
      (fun q => generic_minimal_iff_elim_left_raw Hm
        (ifo_neg q) (IFOImp q IFOFalsum)
        (generic_minimal_neg_equiv Hm q)) p).
Defined.
