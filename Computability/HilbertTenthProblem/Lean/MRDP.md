# MRDP: recursively enumerable if and only if Diophantine

The repository proves both directions of the Matiyasevich–Robinson–Davis–Putnam
theorem for subsets of the natural numbers: a set is recursively enumerable
if and only if it is Diophantine. The public entry point is
[`Diophantine/MRDP.lean`](Diophantine/MRDP.lean). No mathematical axiom is
added for this result.

`Diophantine.mrdp` states that for every recursively enumerable set
`S : Set ℕ`, there are a natural number `k` and an integer polynomial
`P : MvPolynomial (Unit ⊕ Fin k) ℤ` such that

\[
\forall n\in\mathbb N,\qquad
n\in S\ \Longleftrightarrow\
\exists (w_0,\ldots,w_{k-1})\in\mathbb N^k,
\quad P(n,w_0,\ldots,w_{k-1})=0.
\]

The polynomial and the number of witnesses are fixed before the input is
chosen. Membership at zero is included. Witnesses may be zero, and the
interface also permits `k = 0`. Coefficients and polynomial evaluation are
over `ℤ`, so subtraction is ordinary signed subtraction. The theorem is
an existence result; it does not state a numerical degree or witness bound
or supply a practical polynomial-generating algorithm.

`Diophantine.mrdp_iff` proves the full equivalence with that explicit
polynomial representation. `Diophantine.mrdp_dioph_iff` expresses the same
equivalence using Mathlib's `Dioph` predicate.

## Proof chain

The difficult direction is the readable, shortened proof transplanted from
the standalone project into
[`MRDPCore.lean`](Diophantine/Common/MRDPCore.lean). Its declarations retain
the `MRDP` namespace, and `Diophantine.mrdp` forwards directly to
`MRDP.mrdp`. The article-facing `rePred_dioph` adapter recovers Mathlib's
`Dioph` predicate from that finite polynomial. The proof proceeds through
these interfaces:

| Step | Source and proved interface |
|---|---|
| Binomial coefficients and factorials | `MRDP.binomial_diophFn`, `factorial_diophFn`: binomial digits of powers give Diophantine formulas for the arithmetic used in the CRT certificate |
| Bounded universal quantification | `MRDP.boundedForall_dioph`: pairwise coprime moduli and one simultaneous polynomial congruence replace the bounded family of equations |
| Primitive-recursive graphs | `MRDP.recursionTrace_iff`, `primrec_diophFn`: beta-coded finite traces represent arity-indexed primitive recursion; [`PrimitiveRecursiveDioph.lean`](Diophantine/Common/PrimitiveRecursiveDioph.lean) retains the scalar compatibility interfaces |
| A finite integer polynomial for an r.e. set | `MRDP.exists_fin_polynomial`, `mrdp`: finite support reduces witness coordinates to `Fin k`; Mathlib's bounded evaluator and completeness theorem turn semidecider success into one existential bound |
| The article-facing Diophantine predicate | [`RecursivelyEnumerableDioph.lean`](Diophantine/Common/RecursivelyEnumerableDioph.lean): `rePred_dioph` applies [`MathlibDiophFinite.lean`](Diophantine/Common/MathlibDiophFinite.lean)'s `dioph_iff_exists_fin_polynomial` to the core theorem |
| The converse | [`DiophantineEnumerable.lean`](Diophantine/Common/DiophantineEnumerable.lean): `finite_polynomial_rePred`, `dioph_rePred`; a primitive-recursive zero test and unbounded search semidecide the existence of a finite natural witness tuple |

The converse represents integer polynomial evaluation as a difference of
two primitive-recursive natural functions. Their equality is a
primitive-recursive predicate. Finite tuples are encoded as naturals using
one consistent `Primcodable` encoding; unsuccessful decoding falls back to
the zero tuple, and every tuple is recovered from its own encoding. This
also handles the empty witness tuple.

The more general bounded-universal, exact-iteration, and reachability
interfaces in [`DiophantineTrace.lean`](Diophantine/Common/DiophantineTrace.lean)
remain available, together with ProveIt's `PAListCoding` modules.
The new forward MRDP proof does not use them. Their source provenance and
the earlier proof route are recorded in [TRACE_INTEGRATION.md](TRACE_INTEGRATION.md).

## Source ownership and synchronization

The original standalone extraction was made from source revision `dc9aa085`
of this project. Its manifest recorded twenty source modules,
including the old scalar primitive-recursion and cipher-trace route. The
transplant replaces that route at the public MRDP and article RE interfaces;
the broader polynomial and trace APIs remain independently available.

The canonical source is the standalone single-file extraction `MRDP.lean`
(not included here), which builds with Mathlib alone.
`Diophantine/Common/MRDPCore.lean` is a byte-identical copy, so this project
builds the same proof without depending on a second Lake package. This
project retains the full equivalence and the existing article APIs.
Its general finite-polynomial equivalence and scalar primitive-recursion
interfaces remain available to their callers.

## Reproducing the checks

For a focused check while editing the core proof and its adapters, run from
the ProveIt root:

```text
lake build +Diophantine.MRDP +Diophantine.Common.PrimitiveRecursiveDioph
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
```

That checks the MRDP interfaces. The full build below also checks the article
consumers and the other library modules; uncached article proofs can take
substantially longer than the focused build.

From the ProveIt root, run:

```text
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/RecursivelyEnumerableAxioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/CodeCleanupAxioms.lean
```

The [MRDP audit](checks/MRDPAxioms.lean) covers the core and public endpoints,
both directions, the finite-support adapter, and the scalar primitive-recursion
interfaces. Its endpoint checks restate the public propositions, and
its axiom guard accepts only `propext`, `Classical.choice`, and `Quot.sound`.
The other two audits cover article representation clients and shared helpers.
Dependencies are checked transitively, including assumptions inherited
through imported proofs. The dated build and audit receipts are maintained
in [STATUS.md](STATUS.md).

A theorem-dependency audit of the forward endpoint `Diophantine.mrdp`, with
the module prefixes `Diophantine` and `PAListCoding` as the search boundary,
found that no declaration of `PAListCoding` is needed by the new forward
proof. The module prefix
`Diophantine` includes `MRDPCore.lean` even though that file's declarations
are in namespace `MRDP`. A full parent build, a standalone build, and a
source synchronization check establish different facts and are recorded
separately.

This theorem covers the natural-number formulation, with one free input.
It does not by itself certify all statements in the six articles: their
particular equations, operation counts, witness bounds, and structural
results have separate proof obligations in the status register.
