From Coq Require Import List Vector.

From SyntheticComputability Require Import ArithmeticalHierarchySemantic
  EPF SemiDec partial reductions.
From SyntheticComputability.PostsTheorem Require Import PostsTheorem TuringJump.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.
From TuringDegrees Require Import Core Limit.

Definition lift_nat_predicate (P : nat_set) : Vector.t nat 1 -> Prop :=
  fun v => P (Vector.hd v).

Definition nat_sigma_level (n : nat) (P : nat_set) : Prop :=
  isΣsem n (lift_nat_predicate P).

Definition standard_iterated_jump
    {Part : partiality} {unit_encoding : encoding unit}
    {EPF_assm : EPF.EPF} (n : nat) : nat_set :=
  jump_n singleton_zero n.

Lemma nat_predicate_red_lift (P : nat_set) :
  P ⪯ₘ lift_nat_predicate P.
Proof.
  exists (fun x => @Vector.cons nat x 0 (@Vector.nil nat)).
  intros x. reflexivity.
Qed.

Lemma lift_red_nat_predicate (P : nat_set) :
  lift_nat_predicate P ⪯ₘ P.
Proof.
  exists Vector.hd. intros v. reflexivity.
Qed.

Section PostsTheoremForNat.
  Context {Part : partiality}.
  Context {vec_datatype : datatype (Vector.t nat)}.
  Context {list_vec_datatype :
    datatype (fun k => list (Vector.t nat k))}.
  Context {list_bool_datatype : datatype (fun _ => list bool)}.
  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  (** The canonical [n]-fold jump itself lies at arithmetical level
      [Sigma^0_n].  Together with the next theorem this is genuine
      many-one completeness, not merely hardness. *)
  Theorem standard_iterated_jump_sigma n (Hlem : LEM_Σ n) :
    nat_sigma_level n (standard_iterated_jump n).
  Proof.
    pose proof (PostsTheorem
      (fun _ : Vector.t nat 0 => False) (n := n) Hlem) as Hpost.
    destruct Hpost as [_ [_ [Hlevel _]]].
    unfold nat_sigma_level, lift_nat_predicate,
      standard_iterated_jump, singleton_zero.
    destruct PredExt as [HSigma _].
    eapply HSigma; [exact Hlevel|].
    intros v.
    refine (Vector.caseS' v (fun w =>
      jump_n (fun x : nat => x = 0) n (Vector.hd w) <->
      jumpNK n w) _).
    intros x tail.
    refine (Vector.case0 (fun t =>
      jump_n (fun y : nat => y = 0) n
        (Vector.hd (Vector.cons x t)) <->
      jumpNK n (Vector.cons x t)) _ tail).
    reflexivity.
  Qed.

  (** The completeness clause of Post's theorem, specialized from tuples to
      predicates on natural numbers. *)
  Theorem posts_theorem_sigma_many_one_complete (P : nat_set) n :
    LEM_Σ n ->
    nat_sigma_level n P ->
    P ⪯ₘ standard_iterated_jump n.
  Proof.
    intros Hlem HP.
    pose proof (PostsTheorem (lift_nat_predicate P) (n := n) Hlem) as Hpost.
    destruct Hpost as [_ [_ [_ [Hcomplete [_ _]]]]].
    eapply red_m_transitive.
    - apply nat_predicate_red_lift.
    - apply Hcomplete. exact HP.
  Qed.

  Corollary posts_theorem_sigma_turing_complete (P : nat_set) n :
    LEM_Σ n ->
    nat_sigma_level n P ->
    turing_reducible P (standard_iterated_jump n).
  Proof.
    intros Hlem HP. apply red_m_impl_red_T.
    now apply posts_theorem_sigma_many_one_complete.
  Qed.

  (** The relativized semidecidability clause of Post's theorem. *)
  Theorem posts_theorem_oracle_ce (P : nat_set) n (Hlem : LEM_Σ n) :
    nat_sigma_level (S n) P <->
    OracleSemiDecidable (standard_iterated_jump n) P.
  Proof.
    pose proof (PostsTheorem (lift_nat_predicate P) (n := n) Hlem) as Hpost.
    destruct Hpost as [_ [_ [_ [_ [_ Horacle]]]]].
    unfold nat_sigma_level.
    rewrite Horacle. split.
    - intro Hlift.
      eapply red_m_transports_sdec.
      + exact Hlift.
      + apply nat_predicate_red_lift.
    - intro HP.
      eapply red_m_transports_sdec.
      + exact HP.
      + apply lift_red_nat_predicate.
  Qed.
End PostsTheoremForNat.
