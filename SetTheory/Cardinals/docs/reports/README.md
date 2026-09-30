<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

One hundred and thirteen independent mathematical research packages, unpacked
from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all one hundred and thirteen reports, names the problem each one attacks
and the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites and their Booleanizations, ideals, lattice congruences | 19 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, preorder and order polytopes, numerical semigroups, lattice arrays, tropical degree, mesh patterns, skew partitions, polyomino growth | 22 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, Cigler's conjectures, growth and runs, arithmetic numerators | 10 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems, MDS codes, binomial decompositions, Bernoulli entropy | 12 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, Apéry and Motzkin congruences, iterated series, valuations and periodicity | 9 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy, single-sequence OEIS studies, Apéry arrays | 17 |
| [`automata-and-formal-languages/`](automata-and-formal-languages) — shuffle state complexity, DFAO reversal, synchronization, language hierarchies, additive complexity | 7 |
| [`quaternionic-analysis/`](quaternionic-analysis) — slice regularity, Cauchy–Fueter analysis, the global inverse Fueter problem | 1 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`jacobian-conjecture/`](jacobian-conjecture) — fibers of Keller maps: Gao's five-dimensional map, arithmetic fibers and weighted rigidity of the three-variable counterexample | 3 |
| [`galois-theory-and-radicals/`](galois-theory-and-radicals) — bad characteristics of radical solvers, Fourier–Kummer charts, finite separating ranges for sextic resolvents | 2 |
| [`hilbert-tenth-problem/`](hilbert-tenth-problem) — witness-faithful Diophantine certificates for discrete computation; Diophantine laws of probabilistic, quantum and continuous computation | 2 |
| **Total** | **113** |

## Later deliveries

After the move into ProveIt, new reports arrive through
[`docs/incoming`](../../../../docs/incoming/README.md), whose procedure places
every external report outside the surreal package in this collection.  Its
batch 36 (September 2026) added six reports and extended a seventh:

- [`frechet-bounded-character-sites`](ordinals-and-order-types/frechet-bounded-character-sites),
  merged from two manuscripts, continues the non-claim of
  [`frechet-two-valued-obstruction`](ordinals-and-order-types/frechet-two-valued-obstruction)
  about other filter sites;
- [`cofinal-strata-of-finitary-powersets`](ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets)
  gained Parts II and III, merged from four manuscripts that all prove the
  nonuniform height formula it had left open;
- the new category [`jacobian-conjecture/`](jacobian-conjecture) holds three
  reports continuing the Lean/Rocq project `Algebra/JacobianConjecture`
  (one of them merged from two manuscripts on Gao's map `F6`);
- the new category [`galois-theory-and-radicals/`](galois-theory-and-radicals)
  holds one report continuing `Algebra/PolynomialFormulas`;
- [`polyomino-growth-finite-prefix-corrections`](enumerative-combinatorics/polyomino-growth-finite-prefix-corrections)
  continues `Combinatorics/Polyominoes/KlarnerConstant`, whose Lean-verified
  bound on Klarner's constant is `4.5235`; its own bound `4.498` is
  computer-assisted and not formalized.

Later batches extended existing reports rather than adding new ones: batch 38
gave [`adjacency-bounded-132-avoiders`](enumerative-combinatorics/adjacency-bounded-132-avoiders)
a Part II proving `E_m -> 2 log pi`, and batch 39 added parts to
[`slice-regularity-and-fueter-inversion`](quaternionic-analysis/slice-regularity-and-fueter-inversion)
(polynomial periods in every even dimension),
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(height-two preorders; real-rootedness fails),
[`shifted-catalan-hankel-polynomials`](hankel-determinants/catalan-and-ballot/shifted-catalan-hankel-polynomials)
(root collisions for arbitrary multipliers) and
[`dfao-reversal-coloring-obstruction`](automata-and-formal-languages/dfao-reversal-coloring-obstruction)
(the exact three-output maximum).  Batches 40 and 41 added two reports,
[`a003407-dyadic-scaling-rigidity`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a003407-dyadic-scaling-rigidity)
(continuing the Lean project `Combinatorics/Ramsey`) and
[`sextic-block-resolvent-separators`](galois-theory-and-radicals/sextic-block-resolvent-separators)
(continuing `Algebra/PolynomialFormulas`), and extended four: the DFAO report
(Part III: exact binary reversal for every `k >= 4` past an explicit
threshold), the polyomino report (Part II: where the method saturates),
[`insertion-degree-spectra`](automata-and-formal-languages/insertion-degree-spectra)
(binary alphabets suffice) and
[`nonreal-roots-in-iterative-equations`](log-concavity-and-unimodality/nonreal-roots-in-iterative-equations)
(roots on several circles).  Batch 42 extended five reports again: cyclotomic
resonances (shifted Catalan Hankel polynomials), decreasing maps (nonreal
roots), NP-completeness of the height problem via uniquely restricted
matchings (cofinal strata), cactus rigidity (preorder root polytopes), and
depth certificates closing deficits 3 and 4 for A290268 (power-tower
derivative term counts).  Batch 43 extended four: product entropy (Bernoulli
entropy quasiconcavity), the largest jump near the boundary (adjacency-bounded
132-avoiders), nonholonomicity of A003407, and a four-output Part IV of the
DFAO report.  Batch 44 added
[`constrained-crossover-closure`](automata-and-formal-languages/constrained-crossover-closure)
and extended two reports: gamma-positivity for every finite preorder (preorder
root polytopes, Part IV) and the whole affine-in-`z` weighted Keller class
(weighted Keller rigidity, Part II).  Batches 45 to 51 brought nothing to this
collection.  Batch 52 extended three reports: optimal Kummer atlases, exactly
`d(p−1)` charts (specialization-safe radical solvers, Part II), the
macroscopic jump law, merged from two manuscripts (adjacency-bounded
132-avoiders, Part IV), and finite-output games with `q` labels (open-query
membership games, Part II).  Batch 53 extended one: two-endpoint confluence
(shifted Catalan Hankel polynomials, Part IV), the uniform limit for roots
approaching both ends of the spectrum, with an exact even expansion and a
sharp outward scale.  Batch 54 extended one: the exact algebraic degree of
polynomial-coordinate solutions, with nonradical solutions of order-two
iterative equations (nonreal roots in iterative equations, Part IV); its
second collection manuscript was held for batch 55.  Batch 55 extended two:
the preorder root polytopes gained three parts — ultra-log-concave support
polynomials, merged from two manuscripts, with palindromic cores,
approximate counting and exact-counting hardness (Part V); an ADE threshold
and block-locality for signed matching-support stability (Part VI); and the
transversal matroid of a preorder, which determines it up to isomorphism
(Part VII) — and the shifted Catalan Hankel polynomials gained Part V,
collision-uniform expansions for roots meeting away from the endpoints.
Batch 56 extended two: Cigler's Hankel polynomials gained a proof of the
report's experimental rectangular-Schur formula, with exact minimal
recurrences and a corrected reciprocity sign in Cigler's Conjecture 18
(Cigler's Conjecture 16 parity report, Part II), and the open-query
membership games gained exact filter-profile invariants for spaces with a
finite nonempty derived set, answering Part II's attainment question there
(Part III).  Batch 57 extended three: joint limits with a growing shift and a
Catalan (Marchenko–Pastur) inverse-zero law (shifted Catalan Hankel
polynomials, Part VI), a four-test radical-solvability criterion for
irreducible sextics that needs no separating parameter (sextic
block-resolvent separators, Part II), and exact alphabet-size criteria for
concavity of product Tsallis entropy (two-coin counterexamples, Part III).
Batch 58 extended one: the integral Hasse failures of the three-variable
Keller map are Zariski dense in every plane `C = c ≠ 0` and absent from
`C = 0`, with a complete local criterion for completely split fibers and the
count `~ κ(c) T^{2/3}` in square boxes (arithmetic local–global fibers,
Part II).  Batch 59 brought nothing to this collection.  Batch 60 opened the
category [`hilbert-tenth-problem/`](hilbert-tenth-problem) with two reports
merged from nine manuscripts continuing the Lean project
`Computability/HilbertTenthProblem`, and batch 61 added a seventh manuscript
on FIFO queues and tag systems to the first of them:
[`canonical-diophantine-certificates`](hilbert-tenth-problem/canonical-diophantine-certificates)
(seven manuscripts: polynomials whose natural zeros are in bijection with
bounded executions or their trace classes, for guarded translations, Petri
nets, counter schedules, polynomial trajectories, memory logs, queues and tag
systems and rewriting) and
[`probabilistic-quantum-and-continuous-computation`](hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation)
(three: output laws and normalization budgets of probabilistic programs,
undecidable quantum mortality in dimension four, and a continuous
three-outcome trichotomy).

A report that continues a formal project gains no formal status from it:
each README names the project declarations it builds on and says that its
own theorems are not formalized.

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## Merged reports

One hundred and fifty-four archives arrived, in ten deliveries.  Seven of the
resulting reports — the surreal-number ones, including the merged surcomplex
article — were later moved out to a repository of their own, with their git
history, leaving one hundred and four here.  Two different things reduced the count, and the
difference between them is worth keeping straight.

**Duplicates.**  Twenty archives duplicated another: sixteen pairs, three
three-way clusters and one four-way cluster.  Each cluster was merged into a
single report that proves the shared theorem once and keeps everything every
original built on top of it.  Where the originals reached a result by genuinely
different routes, every route is kept and marked as an alternative, with a
sentence on what each one buys.  The manifest names all source archives on a
merged entry and says what was doubled.

**One thematic consolidation.**  Two further reports were folded into a
neighbour for a different reason — not because they repeated it, but because
they shared a subject.  The three reports on the number of terms in the
derivatives of a power tower, for `x^x` (A293239), `x^(x^2)` (A290268) and
`x^(x^x)` (A281434), are now
[`power-tower-derivative-term-counts`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts):
a common framework proved once, then the three original investigations
unabridged, then a part comparing them.  All fifty of their numbered results
survive unchanged, and a record of every edit made to the three source texts
accompanied the merge.  This was editorial, not deduplication — those three
went through the duplicate sweep first and *cleared* it, below.  Their three
theorems are three different theorems, and the merged article is at pains to say
so rather than let a shared setup suggest the answers are connected.

**The tenth delivery was nine manuscripts on one foundation**, and that turned
out to be a different problem from nine manuscripts on one theorem.  All nine
arrived under the name `surcomplex_analysis`, all dated the same day, all
developing holomorphic function theory over `No[i]` on Hahn-supported series.
They were merged into a single article, which has since moved with the rest of
the surreal-number reports to a repository of its own.

Nine attempts at a theorem either agree or they do not.  Nine attempts at a
*foundation* can come out nine slightly different ways that look alike and are
not interchangeable, and they did: of seventeen load-bearing notions, **six are
genuinely inequivalent across the sources**, and a theorem proved under one is
false under another.  The identity theorem, the global maximum principle,
Liouville and the open mapping theorem hold for coherent sections and fail for
germs; sharp Schwarz and Schwarz–Pick hold for lifts and fail for coherent
sections.  Two of the three residue notions disagree numerically at the same
point.  A single ordinary bound in Liouville gives a characterization, not
constancy.  All of this is recorded in the package's `MERGE_NOTES.md` rather
than smoothed over.

**The ninth delivery was ten manuscripts on one question.**  One was an
expository survey of quaternionic analysis; the other nine were independent
attempts at the same follow-up problem, all written the next day, and one of
them shipped a verbatim copy of the survey as its own source context.  They
were merged into a single article rather than catalogued as ten reports.  The
nine agree — on the two obstruction forms, on the criterion, on the affine
monodromy, on the `8m` cokernel and on the energy constant — and that agreement,
from nine separate derivations, is the substance of the entry.  Thirteen
conflicts between them were resolved and recorded; two were mathematical rather
than notational, and either would have produced a false statement in a
mechanical merge.

**The eighth delivery, by contrast, was mostly duplicates.**  Ten archives
arrived and yield six reports.  Four clusters were confirmed at proof level and
merged, one of them against a report already in the tree
([`trapezohedral-minimal-dominating-sets`](graph-theory/trapezohedral-minimal-dominating-sets),
which absorbed an incoming proof of the same A381190 conjecture).  Every
same-proof verdict was put to two adversarial challengers; one challenge
succeeded in part, and it changed the merge: the two A289587 reports refine the
same sequence by *different* statistics — excedances and records — so the merged
article keeps both refinements rather than collapsing them.  Their two local
predicates disagree on 31 of the 321-avoiders of length at most six, the
smallest being `12`.

**The seventh delivery, by contrast, produced no duplicate at all:** the sweep checked every OEIS A-number and every cited arXiv
identifier in the tree against the eighteen, and rejected twelve near-misses on
inspection — among them those same three power-tower reports, and two that
share a Bell-scale saddle-point method on unrelated sequences.  Shared technique
is not a shared theorem.

The largest merges:

| Merged report | Absorbed | Kept apart |
|---|---:|---|
| [`shuffle-six-state-bound`](automata-and-formal-languages/shuffle-six-state-bound) | 3 | three independent finite certifications, two of them with disjoint witness sets |
| [`preorder-q-zeta-reciprocity`](enumerative-combinatorics/preorder-q-zeta-reciprocity) | 2 | three architecturally independent proofs of the same two theorems |
| [`components-forests-and-ordinal-products`](ordinals-and-order-types/friendly-order-types/components-forests-and-ordinal-products) | 1 | two proofs of the Cartesian formula |
| `canonical-forms-need-not-be-subgraphs` (since moved out) | 1 | two non-isomorphic five-vertex witnesses |
| [`multiple-chain-exponential-formula`](enumerative-combinatorics/multiple-chain-exponential-formula) | 1 | two proofs of the identity, plus eleven listed redundancies |

**A pair that an earlier sweep missed, checked and kept separate.**  A
crosscheck during the eighth delivery flagged
[`a348410-all-prime-congruences`](congruences-and-valuations/supercongruences/a348410-all-prime-congruences)
and
[`a352373-signed-binomial-supercongruences`](congruences-and-valuations/supercongruences/a352373-signed-binomial-supercongruences)
as possible duplicates: the second's family
`a_{r,s,t}(n) = [x^{tn}](1+x)^{rn}(1-x)^{sn}` does specialize, at `t = 1` and
`(r,s) = (-beta,-alpha)`, to the first's coefficient, and the two odd-prime
congruences then agree (the first states its modulus by the exact valuation
`v_p(N)` and the second by a declared level, but these carry the same content
once the multiplier is reindexed).

Both articles were then read in full, and **neither contains the other**.
a352373 is general in the extraction step `t`, which a348410 fixes at 1 —
a348410's "change of step" corollary varies the period `d` in `(1-x^d)`, not
the extraction index. a348410 proves, and a352373 does not: the `p = 2` case
with an exact first binary defect and its sharpness (valuation exactly
`3r-3` when both parameters are odd and `m = 1`), a single all-prime bound
`v_p >= 3r - v_p(12)` with each loss shown necessary, sharp common
denominators with both constants minimal, the primitive-cyclic-word
interpretation, a Lambert series and Euler product, algebraic generating
functions by Lagrange reversion, a spacing-three counterexample showing the
conclusion fails at `p = 5` when `1+x^2` is replaced by `1-x^3`, and a
sufficient criterion abstracting the proof beyond the family.

The proofs are also genuinely different arguments, not one argument twice:
a352373 imports Jacobsthal's congruence and uses it throughout, a348410 does
not invoke it at all and instead pairs a quadratic-tail estimate with a
coefficient estimate. **Decision: keep both.** This is the collection's
"incomparable in both directions" shape, and it is recorded here so a later
sweep does not re-litigate it.

Pairs aimed at one problem are not always duplicates, and several were kept
separate on inspection: the two Gonshor product-birthday reports prove the same
bound on domains incomparable in both directions; Cigler's Conjectures 8, 13–15
and 16 are three separate entries from one paper, as are Athanasiadis–Chapoton's
Conjectures 4.9, 5.1 and Question 4.6, Chiozini–Csernák–Soukup's Problems 1.2
and 1.3, and Deb–Sokal's clauses 1.4(c) and 1.4(d).  The earlier sweep kept three clusters separate because their proofs
differed. The September 29 consolidation below combines the Lipparini pair
and the transfinite-word pair while retaining both proof routes. The
friendly-order-type reports remain separate in this pass: their finite
formula overlaps, but their transfinite continuations and certificate
frameworks need a dedicated synthesis.

## Consolidation of 29 September 2026

Four maintained reports are now two, representing five original manuscripts:

| Unified report | Merged material retained |
|---|---|
| [Minimal infinitary ordinal sum](ordinals-and-order-types/ordinal-arithmetic/lipparini-minimal-infinitary-sum/) | Both solutions of Lipparini Problem 6.2: profile/absorption and corrected-block proofs, distinct consequences, both implementations and audits |
| [Finite-alphabet transfinite words](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared/) | Finite-height atom induction plus the existing two-source guarded-block report: selected-tail classification, exact strata, both lower-bound routes and both computational suites |

The collection now has **111** reports, including **19** in ordinals and order
types. Old report directories contain redirects. Every existing destination
label survives; incoming label and support-file mappings are in each report's
`MERGE_NOTES.md`. Original sources remain recoverable in Git. The
[consolidation record](CONSOLIDATION.md) states the review scope, decisions and
fresh validation; it does not upgrade these drafts to formal proofs.

## Large regenerable artifacts

Sixteen bulk artifacts, about 79 MB in total, are deliberately not distributed:
the 200 pair-distance certificates of `dzyga-synchronizing-retract`, the four
certificate databases of `shuffle-six-state-bound`, the 76 magic-positivity
certificates of `magic-positivity-parking-polytopes`, the 1.5 M expression-DAG
records of `a158415-growth-constant`, and nine large CSV or text tables
elsewhere.  Every one is rebuilt byte for byte by its own package's
generator, each package README gives the command, and `.gitignore` keeps a
local rebuild from returning them to the history.  Nothing an article displays
depends on them: worked examples, small certificate sets and the recorded run
summaries are all still shipped.

## Notes on names and packaging

Several reports attack the same published problem, so each directory is named
for its own angle on it rather than for the archive it came from, and merged
directories are named for their combined scope.  The manifest records the
original archive names with every entry.

No package ships a checksum manifest: re-running a verification suite or
rebuilding a PDF changes file hashes, so a stored manifest goes stale on the
first rebuild.
