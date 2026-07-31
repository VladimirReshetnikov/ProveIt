(** * rocq#21701 -- guard checker: argument-less recursive calls and uniform arguments

    THIS FILE IS EXPECTED TO BE REJECTED.  Regression witness, not a build
    target.

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    Sibling of ../GuardChecker/NestedMutualCrossCall.v (rocq#21682): both are
    failures of the *uniform argument* analysis for nested mutual fixpoints, but
    the trigger here is different.  A recursive call that appears without its
    arguments -- bound by a [let], as in [let h := g in h (S p) m'] -- was not
    taken into account when computing which arguments are uniform.  Passing the
    recursion through a [let]-bound alias therefore hid the growth of [p], and
    the resulting [F_let] is accepted with a non-decreasing recursion.

    The consequence is a term convertible to its own successor, from which
    [False] follows by the usual no-cycle argument.

    Upstream: <https://github.com/rocq-prover/rocq/issues/21701>
      filed 2026-03-02, closed.  Found autonomously by Opus 4.6; one of the
      seven proofs of [False] in <https://tristan.st/blog/in_search_of_falsehood>.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2): REJECTED,
    exit code 1, with

      Recursive definition of F_let is ill-formed.
      Recursive call to F_let has principal argument equal to "n" instead of "k".
*)

Section A.
  Variable (F_let : nat -> nat).

  Fixpoint f (p : nat) (m : nat) {struct m} :=
    match m with
    | O => S p
    | S m' =>
      let h := g in
      h (S p) m'
    end
  with g (q : nat) (m : nat) {struct m} :=
    match m with
    | O => S (F_let q)
    | S m' => f q m'
    end.
End A.

(** The guard checker must reject this. *)
Fixpoint F_let (n : nat) : nat :=
  let r :=
    match n with
    | O => O
    | S k => f F_let k n
    end
  in r.

(** Unreachable on a fixed toolchain; kept to show what acceptance costs:
    [F_let 1] becomes convertible to its own predecessor-successor cycle. *)

Theorem cycle n : n = F_let 1 -> match F_let 1 with 0 => False | S n' => n = n' end.
Proof.
  intro e.
  cbn [F_let].
  lazy delta [f].
  lazy beta iota zeta head.
  apply e.
Qed.

Theorem no_cycle n : match n with 0 => False | S n' => n = n' end -> False.
Proof. induction n; eauto. intros e. rewrite <- e in IHn. auto. Qed.

Theorem real_false : False.
Proof. eapply no_cycle. apply cycle. reflexivity. Qed.

Print Assumptions real_false.
(* On a vulnerable toolchain: "Closed under the global context". *)
