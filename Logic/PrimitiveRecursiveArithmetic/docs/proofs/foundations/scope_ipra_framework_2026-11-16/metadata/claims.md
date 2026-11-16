# Claims and verification status

## Inherited checked facts

The report relies on the repository's checked ordinary iPRA syntax and proof
calculus, `Prf PRAAx`; structural substitution, weakening, simultaneous cut,
and existential elimination; primitive-recursive definitions and
quantifier-free induction; arithmetic/order/pairing/search/division libraries;
and the open/scoped Foundation bridge. These facts are attributed to the
inspected ProveIt snapshot.

## New mathematical claims in this archive

The human-readable report gives proofs of:

- the SCOPE certificate escape and residual composition metatheorems;
- fixed bounded-formula reflection, including bounded alternation;
- least accepted bounded naming with a sentinel;
- capped cyclic demand closure and leastness;
- fixed-trace reflection;
- finite strategy and backward-viability theorems;
- exact, quotient, metric, and gap-guarded observation rules;
- height-bound/complete-list equivalence for decidable coded predicates;
- the scope-normalization theorem for fixed finite interaction graphs.

These are **human proofs**, not new Lean-kernel-checked results in this archive.

## Executable evidence

`reference/scope_reference.py` is an exact finite reference implementation.
`reference/test_scope_reference.py` contains 14 tests. They were executed and
passed; the captured output is `validation/python_tests.txt`. The program is
not an object-language proof checker.

## Lean status

`lean/SCOPE/StructuralKernel.lean` is a no-placeholder source-level candidate
using only existing `Prf` operations. It was not elaborated here because the
ProveIt Lean workspace was unavailable in the artifact runtime. The other Lean
files are explicit blueprints; unfinished theorem signatures are comments, not
axioms or admissions. No new kernel-checked theorem is claimed.

## Nonclaims

The archive does not provide a universal primitive-recursive evaluator, exact
discontinuous choice from arbitrary represented data, a convergence rate from
metastability alone, a height cutoff from a cardinality bound, or general
effective versions of Faltings, Siegel, Mordell-Weil, Chebotarev, or comparable
deep producer theorems.
