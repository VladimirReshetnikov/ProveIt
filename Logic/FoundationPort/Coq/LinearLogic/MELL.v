(** Multiplicative-exponential linear logic without units. *)

From Stdlib Require Import Lists.List Sorting.Permutation.

Import ListNotations.

Inductive mell_formula : Type :=
| mell_atom : nat -> mell_formula
| mell_natom : nat -> mell_formula
| mell_tensor : mell_formula -> mell_formula -> mell_formula
| mell_par : mell_formula -> mell_formula -> mell_formula
| mell_bang : mell_formula -> mell_formula
| mell_quest : mell_formula -> mell_formula.

Fixpoint mell_neg (phi : mell_formula) : mell_formula :=
  match phi with
  | mell_atom p => mell_natom p
  | mell_natom p => mell_atom p
  | mell_tensor psi chi => mell_par (mell_neg psi) (mell_neg chi)
  | mell_par psi chi => mell_tensor (mell_neg psi) (mell_neg chi)
  | mell_bang psi => mell_quest (mell_neg psi)
  | mell_quest psi => mell_bang (mell_neg psi)
  end.

Lemma mell_neg_atom : forall p,
  mell_neg (mell_atom p) = mell_natom p.
Proof. reflexivity. Qed.

Lemma mell_neg_natom : forall p,
  mell_neg (mell_natom p) = mell_atom p.
Proof. reflexivity. Qed.

Lemma mell_neg_tensor : forall phi psi,
  mell_neg (mell_tensor phi psi) = mell_par (mell_neg phi) (mell_neg psi).
Proof. reflexivity. Qed.

Lemma mell_neg_par : forall phi psi,
  mell_neg (mell_par phi psi) = mell_tensor (mell_neg phi) (mell_neg psi).
Proof. reflexivity. Qed.

Lemma mell_neg_bang : forall phi,
  mell_neg (mell_bang phi) = mell_quest (mell_neg phi).
Proof. reflexivity. Qed.

Lemma mell_neg_quest : forall phi,
  mell_neg (mell_quest phi) = mell_bang (mell_neg phi).
Proof. reflexivity. Qed.

Theorem mell_neg_involutive : forall phi,
  mell_neg (mell_neg phi) = phi.
Proof.
  induction phi; simpl; congruence.
Qed.

Definition mell_lolli (phi psi : mell_formula) : mell_formula :=
  mell_par (mell_neg phi) psi.

Lemma mell_lolli_def : forall phi psi,
  mell_lolli phi psi = mell_par (mell_neg phi) psi.
Proof. reflexivity. Qed.

Inductive mell_formula_is_quest : mell_formula -> Prop :=
| mell_formula_is_quest_intro : forall phi,
    mell_formula_is_quest (mell_quest phi).

Lemma mell_formula_is_quest_not_atom : forall p,
  ~ mell_formula_is_quest (mell_atom p).
Proof. intros p H. inversion H. Qed.

Lemma mell_formula_is_quest_not_natom : forall p,
  ~ mell_formula_is_quest (mell_natom p).
Proof. intros p H. inversion H. Qed.

Lemma mell_formula_is_quest_not_tensor : forall phi psi,
  ~ mell_formula_is_quest (mell_tensor phi psi).
Proof. intros phi psi H. inversion H. Qed.

Lemma mell_formula_is_quest_not_par : forall phi psi,
  ~ mell_formula_is_quest (mell_par phi psi).
Proof. intros phi psi H. inversion H. Qed.

Lemma mell_formula_is_quest_not_bang : forall phi,
  ~ mell_formula_is_quest (mell_bang phi).
Proof. intros phi H. inversion H. Qed.

Lemma mell_formula_is_quest_quest : forall phi,
  mell_formula_is_quest (mell_quest phi).
Proof. apply mell_formula_is_quest_intro. Qed.

Definition mell_sequent := list mell_formula.

Definition mell_sequent_is_quest (Gamma : mell_sequent) : Prop :=
  forall phi, In phi Gamma -> mell_formula_is_quest phi.

Lemma mell_sequent_is_quest_nil : mell_sequent_is_quest [].
Proof. intros phi H. inversion H. Qed.

Lemma mell_sequent_is_quest_cons : forall phi Gamma,
  mell_sequent_is_quest (phi :: Gamma) <->
  mell_formula_is_quest phi /\ mell_sequent_is_quest Gamma.
Proof.
  intros phi Gamma. split.
  - intro H. split.
    + apply H. now left.
    + intros psi Hpsi. apply H. now right.
  - intros [Hphi HGamma] psi [<- | Hpsi].
    + exact Hphi.
    + exact (HGamma psi Hpsi).
Qed.

Inductive mell_derivation : mell_sequent -> Type :=
| mell_id : forall p,
    mell_derivation [mell_atom p; mell_natom p]
| mell_cut : forall phi Gamma Delta,
    mell_derivation (phi :: Gamma) ->
    mell_derivation (mell_neg phi :: Delta) ->
    mell_derivation (Gamma ++ Delta)
| mell_exchange : forall Gamma Delta,
    mell_derivation Gamma -> Permutation Gamma Delta ->
    mell_derivation Delta
| mell_tensor_rule : forall phi psi Gamma Delta,
    mell_derivation (phi :: Gamma) ->
    mell_derivation (psi :: Delta) ->
    mell_derivation (mell_tensor phi psi :: Gamma ++ Delta)
| mell_par_rule : forall phi psi Gamma,
    mell_derivation (phi :: psi :: Gamma) ->
    mell_derivation (mell_par phi psi :: Gamma)
| mell_bang_rule : forall phi Gamma,
    mell_derivation (phi :: Gamma) ->
    mell_sequent_is_quest Gamma ->
    mell_derivation (mell_bang phi :: Gamma)
| mell_dereliction : forall phi Gamma,
    mell_derivation (phi :: Gamma) ->
    mell_derivation (mell_quest phi :: Gamma).

Definition mell_proof (phi : mell_formula) : Type :=
  mell_derivation [phi].

Definition mell_derivable (Gamma : mell_sequent) : Prop :=
  exists d : mell_derivation Gamma, True.

Definition mell_cast {Gamma Delta}
    (d : mell_derivation Gamma) (e : Gamma = Delta) :
    mell_derivation Delta :=
  match e with eq_refl => d end.

Definition mell_rotate {phi Gamma}
    (d : mell_derivation (phi :: Gamma)) :
    mell_derivation (Gamma ++ [phi]) :=
  @mell_exchange (phi :: Gamma) (Gamma ++ [phi])
    d (Permutation_cons_append Gamma phi).

Theorem mell_eta : forall phi,
  mell_derivation [phi; mell_neg phi].
Proof.
  induction phi as
    [p | p | phi IHphi psi IHpsi | phi IHphi psi IHpsi
     | phi IHphi | phi IHphi].
  - apply mell_id.
  - exact (mell_rotate (mell_id p)).
  - exact
      (@mell_rotate (mell_par (mell_neg phi) (mell_neg psi))
        [mell_tensor phi psi]
        (@mell_par_rule (mell_neg phi) (mell_neg psi)
          [mell_tensor phi psi]
          (@mell_rotate (mell_tensor phi psi)
            [mell_neg phi; mell_neg psi]
            (@mell_tensor_rule phi psi [mell_neg phi] [mell_neg psi]
              IHphi IHpsi)))).
  - exact
      (@mell_par_rule phi psi [mell_tensor (mell_neg phi) (mell_neg psi)]
        (@mell_rotate (mell_tensor (mell_neg phi) (mell_neg psi))
          [phi; psi]
          (@mell_tensor_rule (mell_neg phi) (mell_neg psi) [phi] [psi]
            (@mell_rotate phi [mell_neg phi] IHphi)
            (@mell_rotate psi [mell_neg psi] IHpsi)))).
  - refine (@mell_bang_rule phi [mell_quest (mell_neg phi)] _ _).
    + exact
        (@mell_rotate (mell_quest (mell_neg phi)) [phi]
          (@mell_dereliction (mell_neg phi) [phi]
            (@mell_rotate phi [mell_neg phi] IHphi))).
    + intros psi [<- | H]; [constructor | inversion H].
  - assert (Hquest : mell_sequent_is_quest [mell_quest phi]).
    { intros psi [<- | H]; [constructor | inversion H]. }
    exact
      (@mell_rotate (mell_bang (mell_neg phi)) [mell_quest phi]
        (@mell_bang_rule (mell_neg phi) [mell_quest phi]
          (@mell_rotate (mell_quest phi) [mell_neg phi]
            (@mell_dereliction phi [mell_neg phi] IHphi))
          Hquest)).
Qed.

Definition mell_identity_proof (phi : mell_formula) :
    mell_proof (mell_lolli phi phi) :=
  @mell_par_rule (mell_neg phi) phi []
    (@mell_rotate phi [mell_neg phi] (mell_eta phi)).

Theorem mell_modus_ponens : forall phi psi,
  mell_proof (mell_lolli phi psi) ->
  mell_proof phi ->
  mell_proof psi.
Proof.
  intros phi psi Himp Hphi.
  assert (Himp' : mell_derivation
      [mell_neg (mell_tensor phi (mell_neg psi))]).
  { eapply mell_cast; [exact Himp |].
    simpl. now rewrite mell_neg_involutive. }
  assert (Hbridge : mell_derivation
      [mell_tensor phi (mell_neg psi); mell_neg phi; psi]).
  { exact (@mell_tensor_rule phi (mell_neg psi)
      [mell_neg phi] [psi]
      (mell_eta phi)
      (@mell_rotate psi [mell_neg psi] (mell_eta psi))). }
  exact (@mell_cut phi [] [psi] Hphi
    (@mell_cut (mell_tensor phi (mell_neg psi))
      [mell_neg phi; psi] [] Hbridge Himp')).
Qed.
