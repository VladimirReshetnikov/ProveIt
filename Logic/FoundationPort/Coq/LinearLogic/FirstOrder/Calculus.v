(** One-sided sequent calculus for first-order classical linear logic. *)

From Stdlib Require Import Lists.List Sorting.Permutation Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.LinearLogic.FirstOrder Require Import Formula Rew.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition llfo_sequent (L : language) := list (llfo_proposition L).

Definition llfo_sequent_is_quest {L} (Gamma : llfo_sequent L) : Prop :=
  forall phi, In phi Gamma -> llfo_is_quest phi.

Definition llfo_sequent_negative {L} (Gamma : llfo_sequent L) : Prop :=
  forall phi, In phi Gamma -> llfo_negative 0 phi.

Lemma llfo_sequent_is_quest_nil : forall L,
  llfo_sequent_is_quest (@nil (llfo_proposition L)).
Proof. intros L phi H. inversion H. Qed.

Lemma llfo_sequent_is_quest_cons : forall L (phi : llfo_proposition L) Gamma,
  llfo_sequent_is_quest (phi :: Gamma) <->
  llfo_is_quest phi /\ llfo_sequent_is_quest Gamma.
Proof.
  intros L phi Gamma. split.
  - intro H. split; [apply H; now left |].
    intros psi Hpsi. apply H. now right.
  - intros [Hphi HGamma] psi [<- | Hpsi]; auto.
Qed.

Lemma llfo_sequent_negative_nil : forall L,
  llfo_sequent_negative (@nil (llfo_proposition L)).
Proof. intros L phi H. inversion H. Qed.

Lemma llfo_sequent_negative_cons : forall L (phi : llfo_proposition L) Gamma,
  llfo_sequent_negative (phi :: Gamma) <->
  llfo_negative 0 phi /\ llfo_sequent_negative Gamma.
Proof.
  intros L phi Gamma. split.
  - intro H. split; [apply H; now left |].
    intros psi Hpsi. apply H. now right.
  - intros [Hphi HGamma] psi [<- | Hpsi]; auto.
Qed.

Definition llfo_quest_sequent {L} (Gamma : llfo_sequent L) : llfo_sequent L :=
  map LLQuest Gamma.

Definition llfo_shift_sequent {L} (Gamma : llfo_sequent L) : llfo_sequent L :=
  map llfo_shift Gamma.

Lemma llfo_quest_sequent_is_quest : forall L (Gamma : llfo_sequent L),
  llfo_sequent_is_quest (llfo_quest_sequent Gamma).
Proof.
  intros L Gamma phi Hphi. apply in_map_iff in Hphi.
  destruct Hphi as [psi [<- _]]. constructor.
Qed.

Unset Implicit Arguments.

Inductive llfo_derivation (L : language) : llfo_sequent L -> Type :=
| LLDIdentity : forall phi,
    llfo_derivation L [phi; llfo_neg phi]
| LLDCut : forall phi Gamma Delta,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (llfo_neg phi :: Delta) ->
    llfo_derivation L (Gamma ++ Delta)
| LLDExchange : forall Gamma Delta,
    llfo_derivation L Gamma -> Permutation Gamma Delta ->
    llfo_derivation L Delta
| LLDOne : llfo_derivation L [LLOne]
| LLDFalsum : forall Gamma,
    llfo_derivation L Gamma -> llfo_derivation L (LLFalsum :: Gamma)
| LLDTensor : forall phi psi Gamma Delta,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (psi :: Delta) ->
    llfo_derivation L (LLTensor phi psi :: Gamma ++ Delta)
| LLDPar : forall phi psi Gamma,
    llfo_derivation L (phi :: psi :: Gamma) ->
    llfo_derivation L (LLPar phi psi :: Gamma)
| LLDVerum : forall Gamma,
    llfo_derivation L (LLVerum :: Gamma)
| LLDWith : forall phi psi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (psi :: Gamma) ->
    llfo_derivation L (LLWith phi psi :: Gamma)
| LLDPlusLeft : forall phi psi Gamma,
    llfo_derivation L (psi :: Gamma) ->
    llfo_derivation L (LLPlus phi psi :: Gamma)
| LLDPlusRight : forall phi psi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (LLPlus phi psi :: Gamma)
| LLDOfCourse : forall phi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_sequent_is_quest Gamma ->
    llfo_derivation L (LLBang phi :: Gamma)
| LLDWeakening : forall phi Gamma,
    llfo_derivation L Gamma ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDDereliction : forall phi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDContraction : forall phi Gamma,
    llfo_derivation L (LLQuest phi :: LLQuest phi :: Gamma) ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDAll : forall (phi : llfo_semiproposition L 1) Gamma,
    llfo_derivation L (@llfo_free L 0 phi :: llfo_shift_sequent Gamma) ->
    llfo_derivation L (LLAll phi :: Gamma)
| LLDExs : forall (phi : llfo_semiproposition L 1) Gamma
    (t : syntactic_term L),
    llfo_derivation L
      (llfo_substitute (fun _ : Fin.t 1 => t) phi :: Gamma) ->
    llfo_derivation L (LLExs phi :: Gamma).

Set Implicit Arguments.

Arguments LLDIdentity {L} phi.
Arguments LLDCut {L phi Gamma Delta} _ _.
Arguments LLDExchange {L Gamma Delta} _ _.
Arguments LLDOne {L}.
Arguments LLDFalsum {L Gamma} _.
Arguments LLDTensor {L phi psi Gamma Delta} _ _.
Arguments LLDPar {L phi psi Gamma} _.
Arguments LLDVerum {L} Gamma.
Arguments LLDWith {L phi psi Gamma} _ _.
Arguments LLDPlusLeft {L phi psi Gamma} _.
Arguments LLDPlusRight {L phi psi Gamma} _.
Arguments LLDOfCourse {L phi Gamma} _ _.
Arguments LLDWeakening {L phi Gamma} _.
Arguments LLDDereliction {L phi Gamma} _.
Arguments LLDContraction {L phi Gamma} _.
Arguments LLDAll {L phi Gamma} _.
Arguments LLDExs {L phi Gamma} t _.

Definition llfo_proof {L} (phi : llfo_proposition L) : Type :=
  llfo_derivation L [phi].

Definition llfo_sentence_proof {L} (sigma : llfo_sentence L) : Type :=
  llfo_derivation L [llfo_emb (fun x : Empty_set => match x with end) sigma].

Definition llfo_derivable {L} (Gamma : llfo_sequent L) : Prop :=
  exists d : llfo_derivation L Gamma, True.

Definition llfo_derivation_cast {L Gamma Delta}
    (d : llfo_derivation L Gamma) (e : Gamma = Delta) :
    llfo_derivation L Delta :=
  match e with eq_refl => d end.

Definition llfo_rotate {L phi Gamma}
    (d : llfo_derivation L (phi :: Gamma)) :
    llfo_derivation L (Gamma ++ [phi]) :=
  @LLDExchange L (phi :: Gamma) (Gamma ++ [phi])
    d (Permutation_cons_append Gamma phi).

Definition llfo_inv_rotate {L phi Gamma}
    (d : llfo_derivation L (Gamma ++ [phi])) :
    llfo_derivation L (phi :: Gamma) :=
  @LLDExchange L (Gamma ++ [phi]) (phi :: Gamma)
    d (Permutation_sym (Permutation_cons_append Gamma phi)).

Fixpoint llfo_derivation_height {L Gamma}
    (d : llfo_derivation L Gamma) : nat :=
  match d with
  | LLDIdentity _ => 0
  | LLDCut d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDExchange d0 _ => llfo_derivation_height d0
  | LLDOne => 0
  | LLDFalsum d0 => llfo_derivation_height d0 + 1
  | LLDTensor d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDPar d0 => llfo_derivation_height d0 + 1
  | LLDVerum _ => 0
  | LLDWith d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDPlusLeft d0 => llfo_derivation_height d0 + 1
  | LLDPlusRight d0 => llfo_derivation_height d0 + 1
  | LLDOfCourse d0 _ => llfo_derivation_height d0 + 1
  | LLDWeakening d0 => llfo_derivation_height d0 + 1
  | LLDDereliction d0 => llfo_derivation_height d0 + 1
  | LLDContraction d0 => llfo_derivation_height d0 + 1
  | LLDAll d0 => llfo_derivation_height d0 + 1
  | LLDExs _ d0 => llfo_derivation_height d0 + 1
  end.

Lemma llfo_height_identity : forall L (phi : llfo_proposition L),
  llfo_derivation_height (LLDIdentity phi) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_cut : forall L (phi : llfo_proposition L) Gamma Delta
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (llfo_neg phi :: Delta)),
  llfo_derivation_height (LLDCut d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_exchange : forall L Gamma Delta
    (d : llfo_derivation L Gamma) (p : Permutation Gamma Delta),
  llfo_derivation_height (LLDExchange d p) = llfo_derivation_height d.
Proof. reflexivity. Qed.

Lemma llfo_height_one : forall L,
  llfo_derivation_height (@LLDOne L) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_falsum : forall L Gamma (d : llfo_derivation L Gamma),
  llfo_derivation_height (LLDFalsum d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_tensor : forall L phi psi Gamma Delta
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (psi :: Delta)),
  llfo_derivation_height (LLDTensor d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_par : forall L phi psi Gamma
    (d : llfo_derivation L (phi :: psi :: Gamma)),
  llfo_derivation_height (LLDPar d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_verum : forall L (Gamma : llfo_sequent L),
  llfo_derivation_height (LLDVerum Gamma) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_with : forall L phi psi Gamma
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (psi :: Gamma)),
  llfo_derivation_height (LLDWith d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_plus_left : forall L phi psi Gamma
    (d : llfo_derivation L (psi :: Gamma)),
  llfo_derivation_height (@LLDPlusLeft L phi psi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_plus_right : forall L phi psi Gamma
    (d : llfo_derivation L (phi :: Gamma)),
  llfo_derivation_height (@LLDPlusRight L phi psi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_of_course : forall L phi Gamma
    (d : llfo_derivation L (phi :: Gamma))
    (h : llfo_sequent_is_quest Gamma),
  llfo_derivation_height (LLDOfCourse d h) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_weakening : forall L phi Gamma
    (d : llfo_derivation L Gamma),
  llfo_derivation_height (@LLDWeakening L phi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_dereliction : forall L phi Gamma
    (d : llfo_derivation L (phi :: Gamma)),
  llfo_derivation_height (LLDDereliction d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_contraction : forall L phi Gamma
    (d : llfo_derivation L (LLQuest phi :: LLQuest phi :: Gamma)),
  llfo_derivation_height (LLDContraction d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_all : forall L (phi : llfo_semiproposition L 1) Gamma
    (d : llfo_derivation L (@llfo_free L 0 phi :: llfo_shift_sequent Gamma)),
  llfo_derivation_height (LLDAll d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_exs : forall L (phi : llfo_semiproposition L 1) Gamma
    (t : syntactic_term L)
    (d : llfo_derivation L
      (llfo_substitute (fun _ : Fin.t 1 => t) phi :: Gamma)),
  llfo_derivation_height (LLDExs t d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_cast : forall L Gamma Delta (d : llfo_derivation L Gamma)
    (e : Gamma = Delta),
  llfo_derivation_height (llfo_derivation_cast d e) =
  llfo_derivation_height d.
Proof. intros L Gamma Delta d e. destruct e. reflexivity. Qed.

(** The primitive identity rule already ranges over arbitrary formulas, so the
    source's structural eta expansion has this shorter extensionally exact
    inhabitant. *)
Definition llfo_eta {L} (phi : llfo_proposition L) :
    llfo_derivation L [phi; llfo_neg phi] := LLDIdentity phi.

Definition llfo_identity_proof {L} (phi : llfo_proposition L) :
    llfo_proof (llfo_lolli phi phi) :=
  @LLDPar L (llfo_neg phi) phi [] (llfo_rotate (llfo_eta phi)).

Theorem llfo_modus_ponens : forall L (phi psi : llfo_proposition L),
  llfo_proof (llfo_lolli phi psi) ->
  llfo_proof phi -> llfo_proof psi.
Proof.
  intros L phi psi Himp Hphi.
  assert (Himp' : llfo_derivation L
      [llfo_neg (LLTensor phi (llfo_neg psi))]).
  { eapply llfo_derivation_cast; [exact Himp |].
    simpl. now rewrite llfo_neg_involutive. }
  assert (Hbridge : llfo_derivation L
      [LLTensor phi (llfo_neg psi); llfo_neg phi; psi]).
  { exact (@LLDTensor L phi (llfo_neg psi)
      [llfo_neg phi] [psi]
      (llfo_eta phi) (llfo_rotate (llfo_eta psi))). }
  exact (@LLDCut L phi [] [psi] Hphi
    (@LLDCut L (LLTensor phi (llfo_neg psi))
      [llfo_neg phi; psi] [] Hbridge Himp')).
Qed.

Corollary llfo_excluded_middle : forall L (phi : llfo_proposition L),
  llfo_derivable [LLPar phi (llfo_neg phi)].
Proof.
  intros L phi. exists (@LLDPar L phi (llfo_neg phi) [] (llfo_eta phi)).
  trivial.
Qed.
