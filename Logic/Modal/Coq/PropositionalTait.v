(**
  A one-sided classical Tait calculus for propositional NNF.

  This module ports [Propositional/Tait/Calculus.lean].  Primitive identity
  is restricted to complementary atoms; the structural eta expansion proves
  identity for every NNF formula and supplies the generic one-sided LK
  interface already used throughout the port.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.
From FoundationModal Require Import
  GenericSemantics GenericAdjunctiveSet GenericEntailment GenericCalculus
  PropositionalNNFormula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pnn_sequent (Atom : Type) : Type := list (pnnformula Atom).

Inductive pnn_derivation (Atom : Type) : pnn_sequent Atom -> Type :=
| PNNDIdentity : forall a : Atom,
    @pnn_derivation Atom [PNNAtom a; PNNNegAtom a]
| PNNDCut : forall (p : pnnformula Atom) gamma delta,
    @pnn_derivation Atom (p :: gamma) ->
    @pnn_derivation Atom (pnn_neg p :: delta) ->
    @pnn_derivation Atom (gamma ++ delta)
| PNNDWeakening : forall gamma delta,
    @pnn_derivation Atom gamma ->
    generic_list_subset gamma delta ->
    @pnn_derivation Atom delta
| PNNDTop : @pnn_derivation Atom [PNNTop]
| PNNDOr : forall p q gamma,
    @pnn_derivation Atom (p :: q :: gamma) ->
    @pnn_derivation Atom (PNNOr p q :: gamma)
| PNNDAnd : forall p q gamma,
    @pnn_derivation Atom (p :: gamma) ->
    @pnn_derivation Atom (q :: gamma) ->
    @pnn_derivation Atom (PNNAnd p q :: gamma).

Arguments pnn_derivation Atom gamma : clear implicits.
Arguments PNNDIdentity {Atom} _.
Arguments PNNDCut {Atom p gamma delta} _ _.
Arguments PNNDWeakening {Atom gamma delta} _ _.
Arguments PNNDTop {Atom}.
Arguments PNNDOr {Atom p q gamma} _.
Arguments PNNDAnd {Atom p q gamma} _ _.

Fixpoint pnn_derivation_height {Atom : Type} {gamma : pnn_sequent Atom}
    (d : pnn_derivation Atom gamma) : nat :=
  match d with
  | PNNDIdentity _ => 0
  | PNNDCut dp dn =>
      S (Nat.max (pnn_derivation_height dp) (pnn_derivation_height dn))
  | PNNDWeakening d _ => S (pnn_derivation_height d)
  | PNNDTop => 0
  | PNNDOr d => S (pnn_derivation_height d)
  | PNNDAnd dp dq =>
      S (Nat.max (pnn_derivation_height dp) (pnn_derivation_height dq))
  end.

Definition pnn_derivation_cast {Atom : Type} {gamma delta : pnn_sequent Atom}
    (d : pnn_derivation Atom gamma) (e : gamma = delta) :
    pnn_derivation Atom delta :=
  generic_lk_cast (pnn_derivation Atom) d e.

Lemma pnn_derivation_height_cast :
  forall (Atom : Type) (gamma delta : pnn_sequent Atom)
         (d : pnn_derivation Atom gamma) (e : gamma = delta),
    pnn_derivation_height (pnn_derivation_cast d e) =
    pnn_derivation_height d.
Proof. intros Atom gamma delta d e; destruct e; reflexivity. Qed.

Definition pnn_derivation_rotate {Atom : Type}
    {p : pnnformula Atom} {gamma : pnn_sequent Atom}
    (d : pnn_derivation Atom (p :: gamma)) :
    pnn_derivation Atom (gamma ++ [p]) :=
  PNNDWeakening d (@generic_list_subset_rotate _ p gamma).

Definition pnn_derivation_tensor {Atom : Type}
    {p q : pnnformula Atom} {gamma delta : pnn_sequent Atom}
    (dp : pnn_derivation Atom (p :: gamma))
    (dq : pnn_derivation Atom (q :: delta)) :
    pnn_derivation Atom (PNNAnd p q :: gamma ++ delta) :=
  PNNDAnd
    (PNNDWeakening dp
      (@generic_list_subset_cons_append_right _ p gamma delta))
    (PNNDWeakening dq
      (@generic_list_subset_cons_append_left _ q gamma delta)).

Definition pnn_derivation_top_eta {Atom : Type} :
    pnn_derivation Atom [@PNNTop Atom; PNNBottom].
Proof.
  apply (PNNDWeakening PNNDTop). intros q [-> | H]; [now left | contradiction].
Defined.

Definition pnn_derivation_bottom_eta {Atom : Type} :
    pnn_derivation Atom [@PNNBottom Atom; PNNTop].
Proof.
  apply (PNNDWeakening PNNDTop). intros q [-> | H]; [now right; left | contradiction].
Defined.

Fixpoint pnn_derivation_eta {Atom : Type} (p : pnnformula Atom) :
    pnn_derivation Atom [p; pnn_neg p] :=
  match p with
  | PNNAtom a => PNNDIdentity a
  | PNNNegAtom a => pnn_derivation_rotate (PNNDIdentity a)
  | PNNTop => pnn_derivation_top_eta
  | PNNBottom => pnn_derivation_bottom_eta
  | PNNAnd q r =>
      pnn_derivation_rotate
        (PNNDOr
          (pnn_derivation_rotate
            (pnn_derivation_tensor
              (pnn_derivation_eta q) (pnn_derivation_eta r))))
  | PNNOr q r =>
      PNNDOr
        (pnn_derivation_rotate
          (pnn_derivation_tensor
            (pnn_derivation_rotate (pnn_derivation_eta q))
            (pnn_derivation_rotate (pnn_derivation_eta r))))
  end.

Definition pnn_derivation_close {Atom : Type}
    (p : pnnformula Atom) (gamma : pnn_sequent Atom)
    (hp : generic_list_member p gamma)
    (hn : generic_list_member (pnn_neg p) gamma) :
    pnn_derivation Atom gamma.
Proof.
  apply (PNNDWeakening (pnn_derivation_eta p)).
  intros q [-> | [-> | H]]; [exact hp | exact hn | contradiction].
Defined.

Definition pnn_tait_lk (Atom : Type) :
    generic_one_sided_lk (pnnformula_connectives Atom)
      (pnn_derivation Atom).
Proof.
  refine {| generic_lk_identity := pnn_derivation_eta;
            generic_lk_verum := PNNDTop |}.
  - intros delta gamma d h.
    exact (@PNNDWeakening Atom delta gamma d h).
  - intros p q gamma dp dq. exact (@PNNDAnd Atom p q gamma dp dq).
  - intros p q gamma d. exact (@PNNDOr Atom p q gamma d).
Defined.

Definition pnn_tait_lk_cut (Atom : Type) :
    generic_one_sided_lk_cut (pnnformula_connectives Atom)
      (pnn_derivation Atom).
Proof.
  refine {| generic_lk_cut_base := pnn_tait_lk Atom |}.
  intros p gamma delta dp dn. exact (@PNNDCut Atom p gamma delta dp dn).
Defined.

Definition pnn_tait_proof {Atom : Type} (p : pnnformula Atom) : Type :=
  pnn_derivation Atom [p].

Inductive pnn_tait_symbol (Atom : Type) : Type :=
| PNNTait : pnn_tait_symbol Atom.

Arguments PNNTait {Atom}.

Definition pnn_tait_entailment (Atom : Type) :
    generic_entailment (pnn_tait_symbol Atom) (pnnformula Atom) :=
  {| generic_proof := fun _ p => pnn_tait_proof p |}.

Definition pnn_tait_principal_entailment (Atom : Type) :
    generic_principal_entailment
      (pnn_tait_entailment Atom) (pnn_derivation Atom) PNNTait.
Proof.
  constructor. intro p.
  refine {| generic_equiv_to := fun d => d;
            generic_equiv_from := fun d => d |}; reflexivity.
Defined.

Definition pnn_tait_is_tautology {Atom : Type} (p : pnnformula Atom) : Prop :=
  inhabited (pnn_tait_proof p).
