(** Arithmetic certificates for Sigma-one truth in the standard model.

    The ordinary recognizer theorem in [Semidecidability] deliberately uses
    a lightweight, step-indexed interface.  Here we retain enough structure
    to obtain an [arith_part1] domain certificate.  A Sigma-one formula is
    first put into a formula-specific witness normal form; the witness tree
    is encoded by pairing and Goedel's beta function. *)

From Stdlib Require Import Arith.Arith Bool.Bool Lia
  Logic.FunctionalExtensionality Vectors.Fin.
From Foundation.Vorspiel Require Import Arithmetic BetaEncoding Matrix Part.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy Misc Model.
From Foundation.FirstOrder.Arithmetic.R0 Require Import
  Representation Semidecidability.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma matrix_vec_head_cons : forall A n (a : A) (v : Fin.t n -> A),
  matrix_vec_head (matrix_vec_cons a v) = a.
Proof. reflexivity. Qed.

Lemma matrix_vec_tail_cons : forall A n (a : A) (v : Fin.t n -> A),
  matrix_vec_tail (matrix_vec_cons a v) = v.
Proof.
  intros A n a v. apply functional_extensionality. intro i. reflexivity.
Qed.

(** Evaluation of a fixed arithmetic term is a total arithmetic function. *)
Lemma r0_semiterm_arithmetic1 : forall X n
    (t : semiterm oring_language X n) (fv : X -> nat),
  arithmetic1
    (fun bv => semiterm_val nat_standard_structure bv fv t).
Proof.
  intros X n t fv.
  apply arithmetic1_of_primitive_recursive1_concrete.
  apply r0_semiterm_primitive_recursive.
Qed.

Lemma r0_semiterm_tail_arithmetic1 : forall X n
    (t : semiterm oring_language X n) (fv : X -> nat),
  arithmetic1
    (fun w : Fin.t (S n) -> nat =>
      semiterm_val nat_standard_structure (matrix_vec_tail w) fv t).
Proof.
  intros X n t fv.
  exact (arithmetic1_tail n
    (fun bv => semiterm_val nat_standard_structure bv fv t)
    (r0_semiterm_arithmetic1 t fv)).
Qed.

(** Replace the head coordinate of the input to a total arithmetic function
    by an arithmetic unary transform. *)
Lemma arithmetic1_map_head : forall n
    (f : (Fin.t (S n) -> nat) -> nat) (g : nat -> nat),
  arithmetic1 f -> arithmetic1_unary g ->
  arithmetic1
    (fun v => f (matrix_vec_cons (g (matrix_vec_head v))
      (matrix_vec_tail v))).
Proof.
  intros n f g Hf Hg.
  eapply arithmetic1_comp with
    (f := f)
    (g := fun i v =>
      matrix_vec_cons (g (matrix_vec_head v)) (matrix_vec_tail v) i).
  - exact Hf.
  - intro i.
    refine (@Fin.caseS' n i
      (fun j => arithmetic1
        (fun v : Fin.t (S n) -> nat =>
          matrix_vec_cons (g (matrix_vec_head v))
            (matrix_vec_tail v) j)) _ _).
    + eapply arithmetic1_comp1.
      * exact Hg.
      * apply arithmetic1_proj.
    + intro j. apply arithmetic1_proj.
Qed.

(** Feed a paired existential witness to a checker whose first coordinate is
    its private witness and whose second coordinate is the quantified value. *)
Lemma arithmetic1_unpack_exists : forall n
    (f : (Fin.t (S (S n)) -> nat) -> nat),
  arithmetic1 f ->
  arithmetic1
    (fun v : Fin.t (S n) -> nat =>
      f (matrix_vec_cons (nat_unpair2 (matrix_vec_head v))
        (matrix_vec_cons (nat_unpair1 (matrix_vec_head v))
          (matrix_vec_tail v)))).
Proof.
  intros n f Hf.
  eapply arithmetic1_comp with
    (f := f)
    (g := fun i v =>
      matrix_vec_cons (nat_unpair2 (matrix_vec_head v))
        (matrix_vec_cons (nat_unpair1 (matrix_vec_head v))
          (matrix_vec_tail v)) i).
  - exact Hf.
  - intro i.
    refine (@Fin.caseS' (S n) i
      (fun j => arithmetic1
        (fun v : Fin.t (S n) -> nat =>
          matrix_vec_cons (nat_unpair2 (matrix_vec_head v))
            (matrix_vec_cons (nat_unpair1 (matrix_vec_head v))
              (matrix_vec_tail v)) j)) _ _).
    + eapply arithmetic1_comp1.
      * exact arithmetic1_unpair2.
      * apply arithmetic1_proj.
    + intro j.
      refine (@Fin.caseS' n j
        (fun k => arithmetic1
          (fun v : Fin.t (S n) -> nat =>
            matrix_vec_cons (nat_unpair1 (matrix_vec_head v))
              (matrix_vec_tail v) k)) _ _).
      * eapply arithmetic1_comp1.
        -- exact arithmetic1_unpair1.
        -- apply arithmetic1_proj.
      * intro k. apply arithmetic1_proj.
Qed.

(** In the bounded-universal checker, beta decodes the private witness for
    the current bounded value. *)
Lemma arithmetic1_beta_body : forall n
    (f : (Fin.t (S (S n)) -> nat) -> nat),
  arithmetic1 f ->
  arithmetic1
    (fun w : Fin.t (S (S n)) -> nat =>
      f (matrix_vec_cons
        (nat_beta (matrix_vec_head (matrix_vec_tail w))
          (matrix_vec_head w))
        (matrix_vec_cons (matrix_vec_head w)
          (matrix_vec_tail (matrix_vec_tail w))))).
Proof.
  intros n f Hf.
  eapply arithmetic1_comp with
    (f := f)
    (g := fun i w =>
      matrix_vec_cons
        (nat_beta (matrix_vec_head (matrix_vec_tail w))
          (matrix_vec_head w))
        (matrix_vec_cons (matrix_vec_head w)
          (matrix_vec_tail (matrix_vec_tail w))) i).
  - exact Hf.
  - intro i.
    refine (@Fin.caseS' (S n) i
      (fun j => arithmetic1
        (fun w : Fin.t (S (S n)) -> nat =>
          matrix_vec_cons
            (nat_beta (matrix_vec_head (matrix_vec_tail w))
              (matrix_vec_head w))
            (matrix_vec_cons (matrix_vec_head w)
              (matrix_vec_tail (matrix_vec_tail w))) j)) _ _).
    + eapply arithmetic1_comp2 with (f := nat_beta).
      * exact arithmetic1_beta.
      * apply arithmetic1_proj.
      * apply arithmetic1_proj.
    + intro j.
      refine (@Fin.caseS' n j
        (fun k => arithmetic1
          (fun w : Fin.t (S (S n)) -> nat =>
            matrix_vec_cons (matrix_vec_head w)
              (matrix_vec_tail (matrix_vec_tail w)) k)) _ _).
      * apply arithmetic1_proj.
      * intro k. apply arithmetic1_proj.
Qed.

(** Finite choice can be internalized by the concrete beta encoder without
    any choice axiom. *)
Lemma concrete_beta_finite_choice : forall bound
    (P : nat -> nat -> Prop),
  (forall i, i < bound -> exists witness, P i witness) ->
  exists code, forall i, i < bound -> P i (nat_beta code i).
Proof.
  induction bound as [|bound IH]; intros P Hall.
  - exists 0. intros i Hi. lia.
  - destruct (Hall bound (Nat.lt_succ_diag_r bound))
      as [last Hlast].
    destruct (IH P) as [prefix Hprefix].
    { intros i Hi. apply Hall. lia. }
    exists (beta_encode concrete_beta_sequence_encoder (S bound)
      (fun i => if Nat.eq_dec i bound then last else nat_beta prefix i)).
    intros i Hi.
    rewrite beta_encode_correct by exact Hi.
    destruct (Nat.eq_dec i bound) as [-> | Hne].
    + exact Hlast.
    + apply Hprefix. lia.
Qed.

(** A formula-specific arithmetic witness checker. *)
Definition r0_sigma_one_witnessed {X} (fv : X -> nat) n
    (p : semiformula oring_language X n) : Prop :=
  exists check : (Fin.t (S n) -> nat) -> nat,
    arithmetic1 check /\
    forall bv,
      semiformula_eval nat_standard_structure bv fv p <->
      exists code, 0 < check (matrix_vec_cons code bv).

Theorem r0_sigma_one_witness_normal_form : forall X (fv : X -> nat) n
    (p : semiformula oring_language X n),
  arithmetic_hierarchy X arithmetic_sigma 1 n p ->
  r0_sigma_one_witnessed fv p.
Proof.
  intros X fv.
  set (P := fun n (p : semiformula oring_language X n) =>
    r0_sigma_one_witnessed fv p).
  assert (Hverum : forall n, P n (Semiformula_verum n)).
  { intro n. unfold P, r0_sigma_one_witnessed.
    exists (fun _ : Fin.t (S n) -> nat => 1). split.
    - apply arithmetic1_one.
    - intro bv. cbn [semiformula_eval]. split.
      + intro. exists 0. lia.
      + intro. exact I. }
  assert (Hfalsum : forall n, P n (Semiformula_falsum n)).
  { intro n. unfold P, r0_sigma_one_witnessed.
    exists (fun _ : Fin.t (S n) -> nat => 0). split.
    - apply arithmetic1_zero.
    - intro bv. cbn [semiformula_eval]. split.
      + contradiction.
      + intros [code Hcode]. lia. }
  assert (Hrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_rel r v)).
  { intros n k r v. unfold P, r0_sigma_one_witnessed.
    destruct r.
    - exists (fun w : Fin.t (S n) -> nat =>
        nat_truth_eq
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v Fin.F1))
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v (Fin.FS Fin.F1)))).
      split.
      + eapply arithmetic1_comp2 with (f := nat_truth_eq).
        * unfold arithmetic1_binary. apply arithmetic1_equal.
        * apply r0_semiterm_tail_arithmetic1.
        * apply r0_semiterm_tail_arithmetic1.
      + intro bv.
        cbn [semiformula_eval nat_standard_structure
          oring_standard_structure].
        split.
        * intro Heq. exists 0.
          rewrite nat_truth_eq_positive_iff. exact Heq.
        * intros [code Hcode].
          now apply nat_truth_eq_positive_iff in Hcode.
    - exists (fun w : Fin.t (S n) -> nat =>
        nat_truth_lt
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v Fin.F1))
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v (Fin.FS Fin.F1)))).
      split.
      + eapply arithmetic1_comp2 with (f := nat_truth_lt).
        * unfold arithmetic1_binary. apply arithmetic1_lt.
        * apply r0_semiterm_tail_arithmetic1.
        * apply r0_semiterm_tail_arithmetic1.
      + intro bv.
        cbn [semiformula_eval nat_standard_structure
          oring_standard_structure].
        split.
        * intro Hlt. exists 0.
          rewrite nat_truth_lt_positive_iff. exact Hlt.
        * intros [code Hcode].
          rewrite nat_truth_lt_positive_iff in Hcode. exact Hcode. }
  assert (Hnrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_nrel r v)).
  { intros n k r v. unfold P, r0_sigma_one_witnessed.
    destruct r.
    - exists (fun w : Fin.t (S n) -> nat =>
        nat_truth_inv (nat_truth_eq
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v Fin.F1))
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v (Fin.FS Fin.F1))))).
      split.
      + eapply arithmetic1_comp1 with (f := nat_truth_inv).
        * exact arithmetic1_inv.
        * eapply arithmetic1_comp2 with (f := nat_truth_eq).
          -- unfold arithmetic1_binary. apply arithmetic1_equal.
          -- apply r0_semiterm_tail_arithmetic1.
          -- apply r0_semiterm_tail_arithmetic1.
      + intro bv.
        cbn [semiformula_eval nat_standard_structure
          oring_standard_structure].
        split.
        * intro Hneq. exists 0.
          rewrite nat_truth_inv_positive_iff,
            nat_truth_eq_positive_iff. exact Hneq.
        * intros [code Hcode].
          rewrite nat_truth_inv_positive_iff,
            nat_truth_eq_positive_iff in Hcode. exact Hcode.
    - exists (fun w : Fin.t (S n) -> nat =>
        nat_truth_inv (nat_truth_lt
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v Fin.F1))
          (semiterm_val nat_standard_structure (matrix_vec_tail w) fv
            (v (Fin.FS Fin.F1))))).
      split.
      + eapply arithmetic1_comp1 with (f := nat_truth_inv).
        * exact arithmetic1_inv.
        * eapply arithmetic1_comp2 with (f := nat_truth_lt).
          -- unfold arithmetic1_binary. apply arithmetic1_lt.
          -- apply r0_semiterm_tail_arithmetic1.
          -- apply r0_semiterm_tail_arithmetic1.
      + intro bv.
        cbn [semiformula_eval nat_standard_structure
          oring_standard_structure].
        split.
        * intro Hnlt. exists 0.
          rewrite nat_truth_inv_positive_iff,
            nat_truth_lt_positive_iff. exact Hnlt.
        * intros [code Hcode].
          rewrite nat_truth_inv_positive_iff,
            nat_truth_lt_positive_iff in Hcode. exact Hcode. }
  assert (Hand : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_and p q)).
  { intros n p q _ _
      [pcheck [Hpcheck Hpspec]] [qcheck [Hqcheck Hqspec]].
    unfold P, r0_sigma_one_witnessed in *.
    exists (fun w : Fin.t (S n) -> nat =>
      nat_truth_and
        (pcheck (matrix_vec_cons
          (nat_unpair1 (matrix_vec_head w)) (matrix_vec_tail w)))
        (qcheck (matrix_vec_cons
          (nat_unpair2 (matrix_vec_head w)) (matrix_vec_tail w)))).
    split.
    - eapply arithmetic1_comp2 with (f := nat_truth_and).
      + exact arithmetic1_and.
      + exact (@arithmetic1_map_head n pcheck nat_unpair1
          Hpcheck arithmetic1_unpair1).
      + exact (@arithmetic1_map_head n qcheck nat_unpair2
          Hqcheck arithmetic1_unpair2).
    - intro bv. cbn [semiformula_eval]. split.
      + intros [Hp Hq].
        destruct (proj1 (Hpspec bv) Hp) as [pcode Hpcode].
        destruct (proj1 (Hqspec bv) Hq) as [qcode Hqcode].
        exists (nat_pair pcode qcode).
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
          nat_unpair1_pair, nat_unpair2_pair,
          nat_truth_and_positive_iff. now split.
      + intros [code Hcode].
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons in Hcode.
        rewrite nat_truth_and_positive_iff in Hcode.
        destruct Hcode as [Hpcode Hqcode]. split.
        * apply (proj2 (Hpspec bv)).
          now exists (nat_unpair1 code).
        * apply (proj2 (Hqspec bv)).
          now exists (nat_unpair2 code). }
  assert (Hor : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_or p q)).
  { intros n p q _ _
      [pcheck [Hpcheck Hpspec]] [qcheck [Hqcheck Hqspec]].
    unfold P, r0_sigma_one_witnessed in *.
    exists (fun w : Fin.t (S n) -> nat =>
      nat_truth_or
        (pcheck (matrix_vec_cons
          (nat_unpair1 (matrix_vec_head w)) (matrix_vec_tail w)))
        (qcheck (matrix_vec_cons
          (nat_unpair2 (matrix_vec_head w)) (matrix_vec_tail w)))).
    split.
    - eapply arithmetic1_comp2 with (f := nat_truth_or).
      + exact arithmetic1_or.
      + exact (@arithmetic1_map_head n pcheck nat_unpair1
          Hpcheck arithmetic1_unpair1).
      + exact (@arithmetic1_map_head n qcheck nat_unpair2
          Hqcheck arithmetic1_unpair2).
    - intro bv. cbn [semiformula_eval]. split.
      + intros [Hp | Hq].
        * destruct (proj1 (Hpspec bv) Hp) as [pcode Hpcode].
          exists (nat_pair pcode 0).
          rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
            nat_unpair1_pair, nat_unpair2_pair,
            nat_truth_or_positive_iff. now left.
        * destruct (proj1 (Hqspec bv) Hq) as [qcode Hqcode].
          exists (nat_pair 0 qcode).
          rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
            nat_unpair1_pair, nat_unpair2_pair,
            nat_truth_or_positive_iff. now right.
      + intros [code Hcode].
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons in Hcode.
        rewrite nat_truth_or_positive_iff in Hcode.
        destruct Hcode as [Hpcode | Hqcode].
        * left. apply (proj2 (Hpspec bv)).
          now exists (nat_unpair1 code).
        * right. apply (proj2 (Hqspec bv)).
          now exists (nat_unpair2 code). }
  assert (Hexists : forall n
      (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p -> P n (Semiformula_exists p)).
  { intros n p _ [check [Hcheck Hspec]].
    unfold P, r0_sigma_one_witnessed in *.
    exists (fun v : Fin.t (S n) -> nat =>
      check (matrix_vec_cons (nat_unpair2 (matrix_vec_head v))
        (matrix_vec_cons (nat_unpair1 (matrix_vec_head v))
          (matrix_vec_tail v)))).
    split.
    - exact (@arithmetic1_unpack_exists n check Hcheck).
    - intro bv. cbn [semiformula_eval]. split.
      + intros [x Hx].
        destruct (proj1 (Hspec (matrix_vec_cons x bv)) Hx)
          as [code Hcode].
        exists (nat_pair x code).
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
          nat_unpair1_pair, nat_unpair2_pair. exact Hcode.
      + intros [packed Hpacked].
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons in Hpacked.
        exists (nat_unpair1 packed).
        apply (proj2 (Hspec
          (matrix_vec_cons (nat_unpair1 packed) bv))).
        now exists (nat_unpair2 packed). }
  assert (Hball : forall n (t : semiterm oring_language X n)
      (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p ->
      P n (semiformula_ball_lt arithmetic_lt_operator t p)).
  { intros n t p _ [check [Hcheck Hspec]].
    unfold P, r0_sigma_one_witnessed in *.
    exists (fun w : Fin.t (S n) -> nat =>
      nat_bounded_all
        (semiterm_val nat_standard_structure (matrix_vec_tail w) fv t)
        (fun x => check
          (matrix_vec_cons (nat_beta (matrix_vec_head w) x)
            (matrix_vec_cons x (matrix_vec_tail w))))).
    split.
    - eapply arithmetic1_bounded_all.
      + apply r0_semiterm_tail_arithmetic1.
      + exact (@arithmetic1_beta_body n check Hcheck).
    - intro bv. rewrite r0_semiformula_eval_ball_lt. split.
      + intro Hall.
        assert (Hchoice : forall x,
            x < semiterm_val nat_standard_structure bv fv t ->
            exists witness,
              0 < check (matrix_vec_cons witness
                (matrix_vec_cons x bv))).
        { intros x Hx. apply (proj1 (Hspec (matrix_vec_cons x bv))).
          now apply Hall. }
        destruct (@concrete_beta_finite_choice
          (semiterm_val nat_standard_structure bv fv t)
          (fun x witness =>
            0 < check (matrix_vec_cons witness
              (matrix_vec_cons x bv))) Hchoice) as [code Hcode].
        exists code.
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
          nat_bounded_all_positive_iff.
        exact Hcode.
      + intros [code Hcode].
        rewrite matrix_vec_head_cons, matrix_vec_tail_cons,
          nat_bounded_all_positive_iff in Hcode.
        intros x Hx. apply (proj2 (Hspec (matrix_vec_cons x bv))).
        exists (nat_beta code x). now apply Hcode. }
  intros n p Hp.
  exact (arithmetic_sigma_one_induction Hverum Hfalsum Hrel Hnrel
    Hand Hor Hball Hexists Hp).
Qed.

(** Minimization over a positive total test has a domain exactly when the
    test succeeds somewhere. *)
Lemma arith_find_positive_on_dom_iff : forall n
    (test : (Fin.t (S n) -> nat) -> nat) (bv : Fin.t n -> nat),
  partial_dom (arith_find_positive_on test bv) <->
  exists witness, 0 < test (matrix_vec_cons witness bv).
Proof.
  intros n test bv. split.
  - intros [witness Hmember]. exists witness.
    apply arith_find_positive_on_member_iff in Hmember.
    exact (proj1 Hmember).
  - intros [bound Hbound].
    destruct (@nat_least_decidable_bound
      (fun witness => 0 < test (matrix_vec_cons witness bv))
      (fun witness => lt_dec 0 (test (matrix_vec_cons witness bv)))
      bound Hbound) as [witness [Hsuccess Hleast]].
    exists witness. rewrite arith_find_positive_on_member_iff.
    now split.
Qed.

(** Strict counterpart of [r0_sigma_one_semidecidable]: the recognizer is
    itself certified in the arithmetic partial-recursion calculus. *)
Theorem r0_sigma_one_arithmetically_semidecidable : forall X
    (fv : X -> nat) n (p : semiformula oring_language X n),
  arithmetic_hierarchy X arithmetic_sigma 1 n p ->
  arithmetically_semidecidable
    (fun bv => semiformula_eval nat_standard_structure bv fv p).
Proof.
  intros X fv n p Hp.
  destruct (r0_sigma_one_witness_normal_form fv Hp)
    as [test [Htest Hspec]].
  exists (arith_find_positive_on test). split.
  - now apply arith_part1_find_positive.
  - intro bv. rewrite Hspec, arith_find_positive_on_dom_iff.
    reflexivity.
Qed.
