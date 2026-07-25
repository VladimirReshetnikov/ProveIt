From Coq Require Import List.

From SyntheticComputability Require Import EPF partial.
From SyntheticComputability.PostsTheorem Require Import KleenePostTheorem TuringJump.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.
From TuringDegrees Require Import Core.

Section KleenePostGeneric.
  Context {Part : partiality}.

  (** Kleene--Post in exactly the abstract oracle-enumerator interface used by
      the upstream constructive development. *)
  Theorem kleene_post_incomparable
      (list_encode : list bool -> nat)
      (list_decode : nat -> list bool)
      (list_decode_encode : forall s, list_decode (list_encode s) = s)
      (Xi : nat -> Functional nat bool nat bool)
      (Xi_computable : forall n, OracleComputable (Xi n))
      (Xi_surjective : forall F, OracleComputable F ->
         exists c, forall R x b, Xi c R x b <-> F R x b) :
    exists A B : nat_set, turing_incomparable A B.
  Proof.
    unfold turing_incomparable.
    eapply KleenePost
      with (lenum := list_encode) (lenum' := list_decode) (Xi := Xi);
      eauto.
  Qed.

  Corollary turing_degrees_not_linear_generic
      (list_encode : list bool -> nat)
      (list_decode : nat -> list bool)
      (list_decode_encode : forall s, list_decode (list_encode s) = s)
      (Xi : nat -> Functional nat bool nat bool)
      (Xi_computable : forall n, OracleComputable (Xi n))
      (Xi_surjective : forall F, OracleComputable F ->
         exists c, forall R x b, Xi c R x b <-> F R x b) :
    ~ (forall A B : nat_set,
         turing_reducible A B \/ turing_reducible B A).
  Proof.
    intros Hlinear.
    destruct (kleene_post_incomparable
      (list_encode := list_encode) (list_decode := list_decode)
      (Xi := Xi) list_decode_encode Xi_computable Xi_surjective)
      as (A & B & HnAB & HnBA).
    destruct (Hlinear A B); contradiction.
  Qed.
End KleenePostGeneric.

Section KleenePostEPF.
  Context {Part : partiality}.
  Context {bool_encoding : encoding bool}.
  Context {EPF_assm : EPF.EPF}.

  Lemma chi_slice_computable n : OracleComputable (χ n).
  Proof.
    eapply OracleComputable_ext.
    - eapply computable_precompose with (g := fun x => (n, x)).
      apply computable_b.
    - reflexivity.
  Qed.

  Lemma chi_enumerates_oracle_functionals :
    forall F, OracleComputable F ->
      exists c, forall R x b, χ c R x b <-> F R x b.
  Proof.
    intros F HF. now apply surjective_b.
  Qed.

  (** With EPF, the only remaining data are a constructive coding of finite
      Boolean strings by naturals. *)
  Theorem kleene_post_from_epf
      (list_encode : list bool -> nat)
      (list_decode : nat -> list bool)
      (list_decode_encode : forall s, list_decode (list_encode s) = s) :
    exists A B : nat_set, turing_incomparable A B.
  Proof.
    eapply kleene_post_incomparable
      with (list_encode := list_encode) (list_decode := list_decode)
           (Xi := χ); eauto using chi_slice_computable,
                                chi_enumerates_oracle_functionals.
  Qed.

  Corollary turing_degrees_not_linear
      (list_encode : list bool -> nat)
      (list_decode : nat -> list bool)
      (list_decode_encode : forall s, list_decode (list_encode s) = s) :
    ~ (forall A B : nat_set,
         turing_reducible A B \/ turing_reducible B A).
  Proof.
    intros Hlinear.
    destruct (kleene_post_from_epf
      (list_encode := list_encode) (list_decode := list_decode)
      list_decode_encode) as (A & B & HnAB & HnBA).
    destruct (Hlinear A B); contradiction.
  Qed.
End KleenePostEPF.
