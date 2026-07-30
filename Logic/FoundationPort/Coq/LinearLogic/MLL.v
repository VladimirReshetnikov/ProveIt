(** Multiplicative linear logic without units. *)

From Stdlib Require Import Lists.List Sorting.Permutation.

Import ListNotations.

Inductive mll_formula : Type :=
| mll_atom : nat -> mll_formula
| mll_natom : nat -> mll_formula
| mll_tensor : mll_formula -> mll_formula -> mll_formula
| mll_par : mll_formula -> mll_formula -> mll_formula.

Fixpoint mll_neg (phi : mll_formula) : mll_formula :=
  match phi with
  | mll_atom p => mll_natom p
  | mll_natom p => mll_atom p
  | mll_tensor psi chi => mll_par (mll_neg psi) (mll_neg chi)
  | mll_par psi chi => mll_tensor (mll_neg psi) (mll_neg chi)
  end.

Lemma mll_neg_atom : forall p,
  mll_neg (mll_atom p) = mll_natom p.
Proof. reflexivity. Qed.

Lemma mll_neg_natom : forall p,
  mll_neg (mll_natom p) = mll_atom p.
Proof. reflexivity. Qed.

Lemma mll_neg_tensor : forall phi psi,
  mll_neg (mll_tensor phi psi) = mll_par (mll_neg phi) (mll_neg psi).
Proof. reflexivity. Qed.

Lemma mll_neg_par : forall phi psi,
  mll_neg (mll_par phi psi) = mll_tensor (mll_neg phi) (mll_neg psi).
Proof. reflexivity. Qed.

Theorem mll_neg_involutive : forall phi,
  mll_neg (mll_neg phi) = phi.
Proof.
  induction phi; simpl; congruence.
Qed.

Definition mll_lolli (phi psi : mll_formula) : mll_formula :=
  mll_par (mll_neg phi) psi.

Lemma mll_lolli_def : forall phi psi,
  mll_lolli phi psi = mll_par (mll_neg phi) psi.
Proof. reflexivity. Qed.

Definition mll_sequent := list mll_formula.

Inductive mll_derivation : mll_sequent -> Type :=
| mll_id : forall p,
    mll_derivation [mll_atom p; mll_natom p]
| mll_cut : forall phi Gamma Delta,
    mll_derivation (phi :: Gamma) ->
    mll_derivation (mll_neg phi :: Delta) ->
    mll_derivation (Gamma ++ Delta)
| mll_exchange : forall Gamma Delta,
    mll_derivation Gamma -> Permutation Gamma Delta ->
    mll_derivation Delta
| mll_tensor_rule : forall phi psi Gamma Delta,
    mll_derivation (phi :: Gamma) ->
    mll_derivation (psi :: Delta) ->
    mll_derivation (mll_tensor phi psi :: Gamma ++ Delta)
| mll_par_rule : forall phi psi Gamma,
    mll_derivation (phi :: psi :: Gamma) ->
    mll_derivation (mll_par phi psi :: Gamma).

Definition mll_proof (phi : mll_formula) : Type :=
  mll_derivation [phi].

Definition mll_derivable (Gamma : mll_sequent) : Prop :=
  exists d : mll_derivation Gamma, True.

Definition mll_cast {Gamma Delta}
    (d : mll_derivation Gamma) (e : Gamma = Delta) :
    mll_derivation Delta :=
  match e with eq_refl => d end.

Definition mll_rotate {phi Gamma}
    (d : mll_derivation (phi :: Gamma)) :
    mll_derivation (Gamma ++ [phi]) :=
  @mll_exchange (phi :: Gamma) (Gamma ++ [phi])
    d (Permutation_cons_append Gamma phi).

Theorem mll_identity : forall phi,
  mll_derivation [phi; mll_neg phi].
Proof.
  induction phi as
    [p | p | phi IHphi psi IHpsi | phi IHphi psi IHpsi].
  - apply mll_id.
  - exact (mll_rotate (mll_id p)).
  - exact
      (@mll_rotate (mll_par (mll_neg phi) (mll_neg psi))
        [mll_tensor phi psi]
        (@mll_par_rule (mll_neg phi) (mll_neg psi)
          [mll_tensor phi psi]
          (@mll_rotate (mll_tensor phi psi)
            [mll_neg phi; mll_neg psi]
            (@mll_tensor_rule phi psi [mll_neg phi] [mll_neg psi]
              IHphi IHpsi)))).
  - exact
      (@mll_par_rule phi psi [mll_tensor (mll_neg phi) (mll_neg psi)]
        (@mll_rotate (mll_tensor (mll_neg phi) (mll_neg psi))
          [phi; psi]
          (@mll_tensor_rule (mll_neg phi) (mll_neg psi) [phi] [psi]
            (@mll_rotate phi [mll_neg phi] IHphi)
            (@mll_rotate psi [mll_neg psi] IHpsi)))).
Qed.

Definition mll_identity_proof (phi : mll_formula) :
    mll_proof (mll_lolli phi phi) :=
  @mll_par_rule (mll_neg phi) phi []
    (@mll_rotate phi [mll_neg phi] (mll_identity phi)).

Theorem mll_modus_ponens : forall phi psi,
  mll_proof (mll_lolli phi psi) ->
  mll_proof phi ->
  mll_proof psi.
Proof.
  intros phi psi Himp Hphi.
  assert (Himp' : mll_derivation [mll_neg (mll_tensor phi (mll_neg psi))]).
  { eapply mll_cast; [exact Himp |].
    simpl. now rewrite mll_neg_involutive. }
  assert (Hbridge : mll_derivation
      [mll_tensor phi (mll_neg psi); mll_neg phi; psi]).
  { exact (@mll_tensor_rule phi (mll_neg psi)
      [mll_neg phi] [psi]
      (mll_identity phi)
      (@mll_rotate psi [mll_neg psi] (mll_identity psi))). }
  exact (@mll_cut phi [] [psi] Hphi
    (@mll_cut (mll_tensor phi (mll_neg psi))
      [mll_neg phi; psi] [] Hbridge Himp')).
Qed.

Corollary mll_excluded_middle : forall phi,
  mll_derivable [mll_par phi (mll_neg phi)].
Proof.
  intro phi.
  exists (@mll_par_rule phi (mll_neg phi) [] (mll_identity phi)).
  trivial.
Qed.
