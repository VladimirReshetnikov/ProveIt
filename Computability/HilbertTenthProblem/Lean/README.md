# Lean 4 formalization of the six articles

A Lean 4 / Mathlib project that formalizes the mathematical essence of the
six corrected articles in [`../Papers/`](../Papers/README.md). **No new axioms may be introduced**
under the project owner's updated 2026-09-14 policy. Existing verified
results may be reused from Mathlib or other Lean developments. The earlier
pre-1980 and elementary-fact axiom allowances are superseded; no project
mathematical axiom was introduced under them. Existing proofs are retained,
and transitive axiom audits identify the dependencies of each published
milestone. Results may be borrowed from
the rest of ProveIt (in particular its Busy Beaver library) and from Cameron Freer's
`hilbert10` (Lean 4 DPRM development, bibliography entry 40).

## Layout

The **MRDP theorem** is available as `Diophantine.mrdp`: every recursively
enumerable `S : Set ℕ` has a fixed integer polynomial with finitely many
natural witnesses whose solvability is equivalent to membership, including
at zero. `Diophantine.mrdp_iff` proves the full equivalence, and
`Diophantine.mrdp_dioph_iff` uses Mathlib's `Dioph` interface. See the
[MRDP proof guide](MRDP.md) for contracts, dependencies, and audit commands.

The forward proof is the readable, shortened standalone development in
[`Common/MRDPCore.lean`](Diophantine/Common/MRDPCore.lean), with all its
declarations in namespace `MRDP`. This is a byte-identical copy of the
standalone single-file MRDP extraction `MRDP.lean` (not included here).

After this milestone, new article formalization is paused by the project
owner. The active phase reviews and simplifies the existing code, extracts
shared helpers, removes duplication, and improves comments while preserving
the proved statements and their mathematical meaning. Generalize results and
strengthen them where useful, retaining existing interfaces for callers.
The [code review](CODE_REVIEW.md) records the first cleanup batch and its
reproducible kernel and axiom checks.

```text
Lean/                                the `Diophantine` library of ProveIt's root Lake workspace
├── Diophantine.lean                 root module importing the project library
├── checks/*Axioms.lean              reproducible transitive axiom audits
└── Diophantine/
    ├── MRDP.lean                   every r.e. natural set is Diophantine; full equivalence
    ├── Common/MRDPCore.lean        synchronized standalone forward MRDP proof
    ├── Common/…                    Pell arithmetic; Dioph adapters; finite traces; RE predicates
    ├── Paper1976/…                  prime polynomials, nth-prime graph, certificates, constancy
    ├── Paper1984/…                  masking ≼, Lucas lemma, (8)–(13), register-machine encoding
    ├── Paper1982/…                  Theorems 1–3; §5 coding, packing, and full polynomial system
    ├── Paper1978/…                  Lemmas 2.1, 2.2, Divisor Lemma, Bounded Quantifier Theorem
    ├── Paper1980/…                  the announcement: single-parameter index reduction; Theorems 1–3 and (58, 4) reuse Paper1982
    └── Paper1974/…                  Σ, SH, SC, H on ProveIt's machine model; Theorem 1, Theorem 2
```

## Conventions

- One Lean theorem per numbered statement of the articles, named after the
  article and the statement (`JSWW1976.lemma_2_3`, `Jones1982.lemma_2_16`,
  …), with a docstring quoting the statement.
- Do not introduce new axioms. Unproved statements remain explicit gaps
  in `STATUS.md`; they must not be reported as completed proofs. Published
  proof milestones contain no `sorry` or `admit`. The repository currently
  has no project mathematical axioms and no `Diophantine/Axioms.lean` file.
- Variables range over ℕ exactly as in the articles; positive-integer
  conventions (1980, 1982) are stated with explicit `0 < x` hypotheses.

## Building

The library is `Diophantine` in ProveIt's root Lake workspace. From the
ProveIt root:

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '2'
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
```

The finite-trace closure uses ProveIt's own `PAListCoding` library
(`Logic/PeanoArithmetic/ListCoding/Lean/`). Its module `PAListCoding.ExactTrace`
holds the exact-iteration and beta-trace facts apart from
`TetrationDiophantine`, so that this library does not import the Foundation
library, whose `Matrix` lemmas clash with Mathlib modules in this library's
import closure. The dated records in `STATUS.md`, `TRACE_INTEGRATION.md` and
the other notes cite files by an earlier layout: `lean/` is `Lean/`,
`current/` is `../Papers/`, and `vendor/pa-list-coding` is `PAListCoding`.

## Status

See `STATUS.md` for the per-statement table and the article-defect log kept
while formalizing.

The agreed **1980 scope** is Theorems 1–3 and an **abridged Theorem 4
containing only the proved universal pair `(58, 4)`**. The other fifteen
reported pairs are excluded for now; Theorem 5 is intentionally excluded.
The [1980 formalization audit](PAPER1980_AUDIT.md) gives the exact theorem
contracts, source crosswalk, exclusions, and validation receipts. In
particular, the input is positive, the printed systems use positive
witnesses, and the quartic degree is measured in the input and 58 witnesses
after fixing the three index parameters. The natural witnesses of the
shifted quartic correspond to positive witnesses of its quadratic system.

`Jones1980.rePred_single_parameter_systems` in
[SingleParameter.lean](Diophantine/Paper1980/SingleParameter.lean) proves
the article's reduction to one index parameter. One positive code is fixed
for all positive inputs; the equation `indexCode z u y = v` introduces the
three positive witnesses `z`, `u`, and `y`, increasing the printed systems'
witness counts from 12, 14, and 28 to 15, 17, and 31. This is a proved
existential reduction and makes no additional decoder or effective
enumeration claim.

The 1982 Theorem 1 is available as `Jones1982.theorem_1`, for an admissible
coding triple and a normalized polynomial of degree at most four, with any
number `ν ≥ 1` of witness variables. `Jones1982.theorem_1_representation`
constructs such a triple once for all positive inputs. The printed exponent
`5^60` is recovered by setting `ν = 58`. The recursively enumerable
corollaries and the universal pair `(58, 4)` are described below.

`Jones1982.theorem_2` uses the same polynomial and index hypotheses and
replaces the three binomial coefficients with one central binomial
coefficient. The packing bounds follow from the displayed common equations,
without assuming the carry conditions to be recovered. `PowerExtension.lean`
and `ProductPell.lean` supply Lemmas 2.26 and 2.27.

`Jones1982.theorem_3` proves the complete eighteen-equation polynomial
system with twenty-eight strictly positive witnesses, under the same
polynomial and index hypotheses. `theorem_3_representation` constructs one
positive coding triple that works for all positive inputs. The two ratio
conversion proofs explicitly construct the positive Pell quotients and
approximation slack, and recover the power-of-two condition in the
converse. All subtraction in the polynomial equations is over `ℤ`.

`Jones1982.short_master` proves the shorter coding equivalence of §5,
and `short_master_packed` replaces its three carry tests by
`N² ∣ C(2R,R)`, where `N = 16zQ⁵`. Both retain `Q = B^(5^(ν+1))`
and `b = 2^w`, with all twelve witnesses strictly positive. The proof
constructs a sufficiently large base for (D8), handles the possible top
digit of `e`, and proves the block bounds before imposing any carry test.
The size chain for Lemma 2.26 is also available without assuming `Q = B^L`.

`Jones1982.short_polynomial_master` now eliminates those powers and the
central-binomial test through the full (D1)–(D37) system. Its record exposes
all 53 scalar witnesses, of which 52 are positive and `D₀` is signed.
`short_polynomial_representation` constructs one positive coding triple
for all positive inputs of the supplied normalized polynomial. The two
Pell directions use the printed `F²−A` formula and construct positive
quotients for both first-coordinate congruences. `short_ratio_iff` checks
the literal rational interpretation of (D21).

`ShortQuadratic.lean` defines the 36 retained variables and 22 auxiliaries
and all 46 residual polynomials. Lean verifies the counts, the quadratic
degree bound of every residual, the quartic bound of their sum of squares,
and equivalence between vanishing of the sum and of every residual.
These bounds count the input `x` but keep `z,u,y,L` as fixed coefficients.
The witness-plus-one transform preserves the degree and evaluation
semantics. `ShortQuadratic.index_normalized` proves that, at an admissible
index, the shifted quartic is nonzero when all 58 witnesses are zero,
for every integer input. No extra normalization witness is needed.

`Jones1982.short_polynomial_iff_quadratic` proves that these substitutions
and auxiliary equations preserve solvability in both directions, including
positivity of every constructed witness. `ShortQuadratic.quartic58` renames
the shifted sum of squares into `MvPolynomial (Fin 59) ℤ`, preserving input
coordinate zero. `wset_quartic58_iff` proves the existential conversion
between nonnegative quartic witnesses and positive quadratic witnesses.
`short_quartic_master` and `short_quartic_representation` give the resulting
representation of every positive input of a supplied normalized quartic,
with one fixed positive coding triple, degree at most four, and normalization.

`EnumerationQuadratic.lean` uses the proved 1978 enumeration to give a
finite integer addition-and-multiplication system for each `W n`.
`EnumerationQuartic.lean` splits each integer node into a difference of
two natural witnesses and adds a guard witness equal to one. Its explicit
polynomial has `6*n+7` witnesses, degree at most four, and normalization.
`Jones1982.diophantine_quartic58` composes this construction with §5:
every `Jones1978.IsDiophantine` set has a normalized 58-witness quartic
representation on positive inputs, regardless of its original polynomial's
degree or number of variables.

`MathlibPolynomial.lean` identifies Mathlib's inductive `IsPoly` functions
with evaluations of integer multivariate polynomials, without requiring a
finite variable type. `MathlibDiophFinite.lean` enumerates only the witness
coordinates in the polynomial's finite support, retaining all input
coordinates. `Jones1978.isDiophantine_iff_mathlib_dioph` then proves the
equivalence of the two set definitions for every natural input, including
zero. Intersection and union closure and the Diophantine representation of
each fixed-base power set follow from Mathlib's proved constructions.

`Jones1982.mathlib_dioph_quartic58` exposes the 58-witness theorem directly
for Mathlib Diophantine sets. `powers_quartic58` applies it to
`{x | ∃ n, a^n = x}` for every natural base `a`, including zero and one.
The quartic representation retains the positive-input restriction and
chooses one polynomial for all those inputs.

`DiophantinePairing.lean` proves Diophantine closure under Mathlib's
`Nat.pair` and both `Nat.unpair` projections. The pairing proof follows
its two polynomial branches; each inverse projection existentially supplies
the other coordinate. `DiophantineTrace.lean` assembles twelve vendored
`PAListCoding` proof modules into unconditional bounded-universal and
exact-iteration closure. These remain available as independent library
interfaces. The forward MRDP proof uses `MRDPCore.lean` instead: a direct
CRT certificate eliminates bounded universal quantifiers, and a beta-coded
finite trace represents primitive recursion. `PrimitiveRecursiveDioph.lean`
adapts its arity-indexed `MRDP.primrec_diophFn` theorem to the existing
scalar `Nat.Primrec` interfaces, retaining arbitrary Diophantine input
substitutions.

`Diophantine.rePred_dioph` proves that every Mathlib `REPred` on the natural
numbers is Diophantine, including its behavior at zero. It obtains the finite
polynomial from `MRDP.mrdp` and applies the existing finite-polynomial
equivalence to recover Mathlib's `Dioph` predicate. The core proof uses a
fixed semidecider and Mathlib's bounded evaluator. This supplies the representation
bridge used by `Jones1978.isDiophantine_of_rePred` and
`Jones1982.rePred_quartic58`; no DPRM axiom is introduced.

`Jones1982.universal_quartic58` chooses one joint integer polynomial in
`Fin 3 ⊕ Fin 59` before the represented recursively enumerable set. A second
compression fixes the exponent globally at `L4 58 = 5^59`. Three positive
parameters then specialize this polynomial to the explicit normalized
quartic, with one input and 58 natural witnesses. Its degree is at most four
after fixing the parameters, matching §5's convention. Membership equivalence
holds for positive inputs. `specialize_jointPolynomial` establishes literal
polynomial equality with the explicit family.

`Jones1982.rePred_printed_systems` supplies one positive coding triple for
all three printed Theorems 1–3 and all positive inputs, with exactly 12, 14,
and 28 strictly positive witnesses respectively. These systems use the
printed exponent `5^60`.

The proof chain, source provenance, and integration boundaries are recorded
in [TRACE_INTEGRATION.md](TRACE_INTEGRATION.md). See `STATUS.md` for validation
receipts and the article statements that remain open. After `lake build`,
run `lake env lean Computability/HilbertTenthProblem/Lean/checks/RecursivelyEnumerableAxioms.lean` to reproduce the
transitive axiom audit of the core, retained trace interfaces, and article clients.

The common relation-combining construction is proved in
`Common/RelationCombining.lean`. For arbitrary integer radicands `Aᵢ` and
integer parameters `B,C,D`, with `B ≠ 0`, `relationCombining_iff` equates
the square conditions, `B ∣ C`, and `D > 0` with a single polynomial
equation in one natural witness. `RelationCombiningComposition.lean`
constructs its ordinary joint polynomial and proves evaluation under
arbitrary polynomial substitutions. Sign invariance removes the formal
radicals; Galois fixed fields and norm separation establish necessity
without assuming independent square classes or nonnegative radicands.

`JSWW1976.theorem_3_9_reduced` eliminates the fourteen capital letters and
retains exactly ten natural witnesses. Its strict polynomial margin
preserves the rational inequality's denominator conditions.
`JSWW1976.TwelveVariable.primePolynomial` is an actual integer
`MvPolynomial (Fin 12) ℤ`; `prime_iff_positive_value` proves that its
positive values on natural assignments are exactly the primes. The shift
from `k` to `k+1` in the reduced criterion includes the prime 2.

The refined construction has separate APIs. `Common/RefinedRelationCombining.lean`
uses individual polynomial weights, a positive divisor, and a nonnegative
dividend; it includes signed radicands, repeated square classes, zero roots,
and the empty family. `Paper1976/RefinedWeightBounds.lean` supplies bounds
valid on every natural assignment, including assignments where the capital
expressions `K,L,R,G` are negative. `FiveSquareGrowth.lean` and
`FiveSquareCriterion.lean` use equation (24) to supply the two growth
inequalities needed by Theorem 3.9 and preserve its ten-witness criterion.
The replacement does not assert the old second square condition.

`Common/RefinedRelationCombiningDegree.lean` counts the degrees of both
radical monomials and their polynomial coefficients, then transports the
bound through exponent halving. `Paper1976/RefinedPolynomialDegrees.lean`
provides the six-square bounds 13376 and 26753 and the five-square bounds
6848 and 13697 for the combined and prime polynomials respectively.
`ExactDegreePrimePolynomial.lean` defines a further construction with exact
degree 13697: multiply the five-square combined polynomial `M` by
`(X 11 + 1)^(6848 - M.totalDegree)` before applying `(X 0 + 2)(1-M²)`.
The multiplier is positive on every natural assignment, so this preserves
the natural zero set and all positive prime values without adding a
coordinate. Exact degree for the unpadded `M` is not asserted.

`Paper1976/PrimeZeroTest.lean` packages Theorem 3 using the nonnegative
polynomial `M = combined²`. With one parameter and eleven natural
witnesses, `2 + k * 0^M` has exactly the primes as its range: a successful
test returns `k+2`, and a failed test returns 2. The exponent is
nonnegative on every assignment and `0^0=1` is explicit. This new module
passes the consolidated build and transitive axiom audit.

The refined degree and application proofs pass the consolidated build;
the completed validation receipt is in [STATUS.md](STATUS.md).
[RELATION_COMBINING_FRONTIER.md](RELATION_COMBINING_FRONTIER.md) records
the formulas, proof interfaces, and the source-only degree estimates for
the older common-weight construction. After the umbrella build, run
`lake env lean Computability/HilbertTenthProblem/Lean/checks/RefinedRelationCombiningAxioms.lean` for the refined
construction's transitive axiom audit. The earlier
`checks/RelationCombiningAxioms.lean` audit remains reproducible for the
original construction and its historical receipt.

The 1976 Theorems 4, 5, and 4.1 are also proved. `JSWW1976.theorem_4`
uses the Diophantine nth-prime graph and Putnam's construction to give a
fixed finite-witness polynomial at every positive index; the separate
fourteen-witness refinement remains open. `JSWW1976.theorem_5` gives an
acyclic primality certificate with 40 addition and 47 multiplication
checks, under the documented convention that equality/domain checks and
fixed numerals are free. `JSWW1976.theorem_4_1` retains complex
coefficients and proves that a polynomial taking only prime values on the
nonnegative integer grid is constant. Their audit files are
`checks/NthPrimeAxioms.lean` and `checks/PrimeCertificatesAxioms.lean`.
