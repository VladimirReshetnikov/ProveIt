(** Standard-natural provability with a proof-code bound.

    Foundation studies the internal predicate saying that a formula has a
    proof whose Goedel number is below [2^e], then diagonalizes its negation.
    The numerical core does not require an internal arithmetic formula: it is
    a general theory of bounded standard proof codes.  We factor that core at
    an arbitrary bound and specialize it to powers of two.

    The source's internal Pi-one formula, its definedness certificate, the
    restricted Goedel fixed point, and the truth/provability theorems for that
    particular sentence remain outside this module.  They require an
    arithmetic proof graph, exponentiation graph, and formula-level
    diagonalization.  No such internal adapter is assumed here. *)

From Stdlib Require Import Arith.PeanoNat Lia.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import
  D1.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The reusable core: [phi] has an accepted standard proof code strictly
    below [bound]. *)
Definition boot_bounded_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (bound phi : nat) : Prop :=
  exists code,
    code < bound /\ @boot_proof L EL T ET code phi.

(** Foundation's restricted predicate is the power-of-two specialization. *)
Definition boot_restricted_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (e phi : nat) : Prop :=
  @boot_bounded_provable L EL T ET (2 ^ e) phi.

Definition boot_sentence_restricted_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (e : nat)
    (sigma : sentence L) : Prop :=
  @boot_restricted_provable L EL T ET e
    (boot_sentence_code EL sigma).

Lemma boot_bounded_provable_witness_iff : forall L EL T ET bound phi,
  @boot_bounded_provable L EL T ET bound phi <->
  exists code,
    code < bound /\ @boot_proof L EL T ET code phi.
Proof. reflexivity. Qed.

Lemma boot_restricted_provable_witness_iff : forall L EL T ET e phi,
  @boot_restricted_provable L EL T ET e phi <->
  exists code,
    code < 2 ^ e /\ @boot_proof L EL T ET code phi.
Proof. reflexivity. Qed.

(** Typed quotation introduces no additional coding side condition: the
    bounded witness proves exactly the quoted proposition. *)
Lemma boot_restricted_quote_witness_iff :
    forall L EL T ET e (p : proposition L),
  @boot_restricted_provable L EL T ET e
      (boot_typed_formula_quote EL p) <->
  exists code,
    code < 2 ^ e /\
    @boot_proof L EL T ET code (boot_typed_formula_quote EL p).
Proof. reflexivity. Qed.

Lemma boot_sentence_restricted_provable_witness_iff :
    forall L EL T ET e (sigma : sentence L),
  @boot_sentence_restricted_provable L EL T ET e sigma <->
  exists code,
    code < 2 ^ e /\
    @boot_proof L EL T ET code (boot_sentence_code EL sigma).
Proof. reflexivity. Qed.

(** Increasing an arbitrary numerical bound preserves bounded provability. *)
Lemma boot_bounded_provable_mono : forall L EL T ET bound bound' phi,
  bound <= bound' ->
  @boot_bounded_provable L EL T ET bound phi ->
  @boot_bounded_provable L EL T ET bound' phi.
Proof.
  intros L EL T ET bound bound' phi Hle [code [Hcode Hproof]].
  exists code. split; [lia | exact Hproof].
Qed.

(** Therefore restricted provability is monotone in the exponent. *)
Lemma boot_restricted_provable_mono : forall L EL T ET e e' phi,
  e <= e' ->
  @boot_restricted_provable L EL T ET e phi ->
  @boot_restricted_provable L EL T ET e' phi.
Proof.
  intros L EL T ET e e' phi He.
  apply boot_bounded_provable_mono.
  now apply Nat.pow_le_mono_r; lia.
Qed.

(** Forgetting the numerical bound yields ordinary code provability. *)
Lemma boot_bounded_provable_to_provable : forall L EL T ET bound phi,
  @boot_bounded_provable L EL T ET bound phi ->
  @boot_provable L EL T ET phi.
Proof.
  intros L EL T ET bound phi [code [_ Hproof]].
  now exists code.
Qed.

Corollary boot_restricted_provable_to_provable : forall L EL T ET e phi,
  @boot_restricted_provable L EL T ET e phi ->
  @boot_provable L EL T ET phi.
Proof.
  intros L EL T ET e phi.
  exact (@boot_bounded_provable_to_provable
    L EL T ET (2 ^ e) phi).
Qed.

(** Restricted sentence provability is sound for the original first-order
    theory because every accepted standard code reconstructs a derivation. *)
Theorem boot_sentence_restricted_provable_sound :
    forall L T EL ET e (sigma : sentence L),
  @boot_sentence_restricted_provable L EL T ET e sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros L T EL ET e sigma Hrestricted.
  apply (@boot_sentence_provable_sound L T EL ET sigma).
  exact (@boot_restricted_provable_to_provable
    L EL T ET e (boot_sentence_code EL sigma) Hrestricted).
Qed.

(** Every natural is below a power of two with one more than that natural as
    exponent.  Keeping this small arithmetic fact local avoids choosing a
    logarithm merely to bound one already-known proof code. *)
Lemma nat_lt_two_pow_succ : forall n, n < 2 ^ S n.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - rewrite Nat.pow_succ_r by lia.
    assert (Hpos : 0 < 2 ^ S n).
    { pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)). lia. }
    lia.
Qed.

(** Exact external characterization: a sentence is a theorem iff it is
    restricted-provable for some exponent.  The forward direction serializes
    a proof and uses the explicit exponent [S code]. *)
Theorem boot_sentence_provable_iff_exists_restricted :
    forall L T EL ET (sigma : sentence L),
  first_order_theory_provable T sigma <->
  exists e,
    @boot_sentence_restricted_provable L EL T ET e sigma.
Proof.
  intros L T EL ET sigma. split.
  - intro Hsigma.
    destruct (@boot_internalize_provability L T EL ET sigma Hsigma)
      as [code Hcode].
    exists (S code), code. split.
    + apply nat_lt_two_pow_succ.
    + exact Hcode.
  - intros [e Hrestricted].
    exact (@boot_sentence_restricted_provable_sound
      L T EL ET e sigma Hrestricted).
Qed.

(** If no proof occurs below a bound, every accepted proof code lies at or
    above that bound.  This is the representation-independent numerical core
    of Foundation's lower bound for proofs of its restricted Goedel sentence. *)
Theorem boot_bounded_proof_code_lower_bound :
    forall L EL T ET bound phi code,
  ~ @boot_bounded_provable L EL T ET bound phi ->
  @boot_proof L EL T ET code phi ->
  bound <= code.
Proof.
  intros L EL T ET bound phi code Hnot Hproof.
  apply Nat.nlt_ge. intro Hcode.
  apply Hnot. exists code. now split.
Qed.

Corollary boot_restricted_proof_code_lower_bound :
    forall L EL T ET e phi code,
  ~ @boot_restricted_provable L EL T ET e phi ->
  @boot_proof L EL T ET code phi ->
  2 ^ e <= code.
Proof.
  intros L EL T ET e phi code.
  exact (@boot_bounded_proof_code_lower_bound
    L EL T ET (2 ^ e) phi code).
Qed.

Corollary boot_sentence_restricted_proof_code_lower_bound :
    forall L EL T ET e (sigma : sentence L) code,
  ~ @boot_sentence_restricted_provable L EL T ET e sigma ->
  @boot_proof L EL T ET code (boot_sentence_code EL sigma) ->
  2 ^ e <= code.
Proof.
  intros L EL T ET e sigma code.
  exact (@boot_restricted_proof_code_lower_bound
    L EL T ET e (boot_sentence_code EL sigma) code).
Qed.
