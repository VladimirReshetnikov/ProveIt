(** Type-valued Hilbert deduction for intuitionistic first-order logic. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus
  GenericEntailment GenericLogicSymbol GenericSemantics
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew.

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
