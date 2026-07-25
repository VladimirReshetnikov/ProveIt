From Coq Require Import List Vector.

From SyntheticComputability Require Import ArithmeticalHierarchySemantic
  Definitions EPF partial.
From SyntheticComputability.PostsProblem Require Import limit_computability.
From SyntheticComputability.PostsTheorem Require Import PostsTheorem TuringJump.
From TuringDegrees Require Import Core Jump.

Definition singleton_zero : nat_set := fun n => n = 0.

Section ShoenfieldLimitLemma.
  Context {Part : partiality}.
  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  Lemma decidable_singleton_zero : decidable singleton_zero.
  Proof.
    exists (fun n => match n with 0 => true | S _ => false end).
    intros [|n]; unfold reflects, singleton_zero; cbn.
    - split; intro H; reflexivity.
    - split; intro H; discriminate H.
  Qed.

  Definition standard_halting : nat_set := turing_jump singleton_zero.

  Lemma singleton_zero_equiv_empty :
    turing_equiv singleton_zero empty_set.
  Proof.
    apply all_decidable_sets_same_degree.
    - apply decidable_singleton_zero.
    - apply decidable_empty_set.
  Qed.

  Lemma standard_halting_equiv_zero_jump :
    turing_equiv standard_halting zero_jump.
  Proof.
    unfold standard_halting, zero_jump.
    now apply jump_respects_degree_equality, singleton_zero_equiv_empty.
  Qed.

  Section Forward.
    Context {vec_datatype : datatype (Vector.t nat)}.
    Context {list_vec_datatype :
      datatype (fun k => list (Vector.t nat k))}.
    Context {list_bool_datatype : datatype (fun _ => list bool)}.

    (** Constructive direction of Shoenfield's limit lemma.  The upstream
        proof needs [LEM_Σ 1], not unrestricted excluded middle. *)
    Theorem limit_computable_turing_reducible_zero_jump (P : nat_set) :
      LEM_Σ 1 ->
      limit_computable P ->
      turing_reducible P zero_jump.
    Proof.
      intros Hlem Hlim.
      transitivity standard_halting.
      - unfold standard_halting, turing_jump, singleton_zero.
        change (turing_reducible P (jump_n (fun n : nat => n = 0) 1)).
        now apply (limit_turing_red_K (k := 0)).
      - apply standard_halting_equiv_zero_jump.
    Qed.
  End Forward.

  (** Reverse direction.  [definite] records the pointwise decisions that a
      constructive proof must use when turning convergence into both sides of
      a characteristic relation. *)
  Theorem turing_reducible_zero_jump_limit_computable (P : nat_set) :
    turing_reducible P zero_jump ->
    definite standard_halting ->
    definite P ->
    limit_computable P.
  Proof.
    intros HP HK Hdef.
    eapply turing_red_K_lim.
    - transitivity zero_jump; [exact HP|].
      apply standard_halting_equiv_zero_jump.
    - exact HK.
    - exact Hdef.
  Qed.

  Section Equivalence.
    Context {vec_datatype : datatype (Vector.t nat)}.
    Context {list_vec_datatype :
      datatype (fun k => list (Vector.t nat k))}.
    Context {list_bool_datatype : datatype (fun _ => list bool)}.

    Theorem shoenfield_limit_lemma (P : nat_set) (Hlem : LEM_Σ 1) :
      definite P ->
      (limit_computable P <-> turing_reducible P zero_jump).
    Proof.
      intro Hdef. split.
      - now apply limit_computable_turing_reducible_zero_jump.
      - intro HP. apply turing_reducible_zero_jump_limit_computable;
          try assumption.
        unfold standard_halting, turing_jump, singleton_zero.
        change (definite (jump_n (fun n : nat => n = 0) 1)).
        now apply def_K.
    Qed.
  End Equivalence.
End ShoenfieldLimitLemma.
