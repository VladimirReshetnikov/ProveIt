(** * rocq#21682 -- guard checker: cross-calls in nested mutual fixpoints

    THIS FILE IS EXPECTED TO BE REJECTED.  It is a regression witness, not a
    build target.

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    The defect: [find_uniform_parameters] in [kernel/inductive.ml] decides which
    parameters of a nested mutual fixpoint are "uniform" -- passed through
    unchanged by every recursive call -- because uniform parameters keep their
    subterm spec from the enclosing context.  It inspected only SELF-recursive
    calls (body [i] calling body [i]) and ignored CROSS-calls (body [i] calling
    body [j], [i <> j]).  A parameter that grows through a cross-call was
    therefore misclassified as uniform.  [drop_uniform_parameters] had the same
    blind spot.

    Below, [f] passes [S p] to [g], so [p]/[q] is not uniform; treating it as
    uniform lets [F] recurse on a non-decreasing argument.

    The upstream fix replaces the self-call test [Int.equal n (nbodies + k - i)]
    with the any-body test [n > k && n <= k + nbodies].

    Upstream: <https://github.com/rocq-prover/rocq/issues/21682>
      filed 2026-02-28, closed 2026-03-04.  Found autonomously by Opus 4.6 and
      turned into a functional proof of [False] by ccz181078; one of the seven
      proofs of [False] reported in
      <https://tristan.st/blog/in_search_of_falsehood>.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2):

      REJECTED at [F], exit code 1, with

        Recursive definition of F is ill-formed.
        Recursive call to F has principal argument equal to "q" instead of "k".

      -- which is exactly the rejection the upstream patch predicted.
*)

(** The guard checker must reject this. *)
Fixpoint F (n : nat) : nat :=
  match n with
  | O => O
  | S k =>
    (fix f (p : nat) (m : nat) {struct m} :=
       match m with O => p | S m' => g (S p) m' end
     with g (q : nat) (m : nat) {struct m} :=
       match m with O => F q | S m' => f q m' end
     for f) k k
  end.

(* On a vulnerable toolchain [F] is accepted and does not terminate on inputs
   that drive the cross-call, which ccz181078 turned into a proof of False. *)
