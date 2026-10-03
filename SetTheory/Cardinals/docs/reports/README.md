<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

One hundred and eighty independent mathematical research packages, unpacked
from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all one hundred and eighty reports, names the problem each one attacks
and the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites and their Booleanizations, ideals, lattice congruences, lexicographic orders of the well-orderings of the reals | 20 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, preorder and order polytopes, numerical semigroups, lattice arrays, tropical degree, mesh patterns, skew partitions, polyomino growth, first pattern failures, pyramidal Frobenius numbers, valley-monotone bargraphs | 25 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, Cigler's conjectures, growth and runs, arithmetic numerators | 10 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems, MDS codes, binomial decompositions, Bernoulli entropy, matching-rank normalization, preorder gamma polynomials | 14 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, Apéry and Motzkin congruences, iterated series, integrality of asymptotic coefficients, valuations and periodicity | 11 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy, single-sequence OEIS studies (power-tower derivative supports, restricted and weighted partitions, excursions and restricted permutations, Fourier peaks, gamma constants, L-convex polyominoes, pattern-avoiding ascent sequences, iterated Bell diagonals, corner polyhedra, powered Catalan and Mahonian numbers, divisor-weighted products, phylogenetic trees and networks, Airy amplitudes of trees and automata, historic and identity trees, Takeuchi numbers, tournament scores, involutions, parabolic cosets and signed permutations, rook paths, cyclic word covers, colored and radix-layer partitions, acyclic orientations, chess placements, football seasons, vincular avoiders, Beta renewals, signed moments, moving zeros and fugacities), Apéry arrays | 67 |
| [`automata-and-formal-languages/`](automata-and-formal-languages) — shuffle state complexity, DFAO reversal, synchronization, language hierarchies, additive complexity, counting accessible and strongly connected automata | 8 |
| [`quaternionic-analysis/`](quaternionic-analysis) — slice regularity, Cauchy–Fueter analysis, the global inverse Fueter problem | 1 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`jacobian-conjecture/`](jacobian-conjecture) — fibers and dynamics of Keller maps: Gao's five-dimensional map, arithmetic fibers, weighted rigidity and dynamical degrees of the three-variable counterexample | 4 |
| [`galois-theory-and-radicals/`](galois-theory-and-radicals) — bad characteristics of radical solvers, Fourier–Kummer charts, finite separating ranges for sextic resolvents | 2 |
| [`hilbert-tenth-problem/`](hilbert-tenth-problem) — witness-faithful Diophantine certificates for discrete computation; Diophantine laws of probabilistic, quantum and continuous computation; recurrence and liveness beyond halting; groups as Diophantine substrates; signal-machine collision certificates; exact events in stochastic and thermal systems; quadratic orthant certificates; polynomial witness histories; smooth Diophantine finalizers | 9 |
| **Total** | **180** |

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
three-outcome trichotomy).  Batch 62 added four Parts to the first of these
(dynamic heaps and fresh names; order-free self-assembly and a sharp degree
threshold for orthant-nonnegative polynomials; priority pumping; conservative
reaction networks with one shared fallback: Parts X–XIII), three Parts from
eight manuscripts to the second (quartic probability landscapes and
reversible equilibria; exact rational and cyclotomic gates; strict and 2-adic
contractions and exact-precision neural networks: Parts V–VII), and opened a
third, [`liveness-beyond-halting`](hilbert-tenth-problem/liveness-beyond-halting)
(two manuscripts: progress deadlines, hyperimmune-free schedules and the
recurrence hierarchy up to Σ¹₁).  Batch 63 added a third manuscript to
[`liveness-beyond-halting`](hilbert-tenth-problem/liveness-beyond-halting)
(an incoming-edge quadratic transition law and planar stack dynamics), a
Part XIV to
[`canonical-diophantine-certificates`](hilbert-tenth-problem/canonical-diophantine-certificates)
(history-free routing certificates and a rank-function bottleneck), and a
Part VIII to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(marked-tree stability).  Batch 64 added a Part IX to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(two-flow bijections and lattice-point sampling), a Part III to
[`arithmetic-local-global-fibers`](jacobian-conjecture/arithmetic-local-global-fibers)
(nonsplit fibers and a `T log T` law), a Part XIV to
[`slice-regularity-and-fueter-inversion`](quaternionic-analysis/slice-regularity-and-fueter-inversion)
(global Fueter inversion beyond finite connectivity), a Part VIII to
[`probabilistic-quantum-and-continuous-computation`](hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation)
(rational tubes for polynomial flows) and a Part V to
[`adjacency-bounded-132-avoiders`](enumerative-combinatorics/adjacency-bounded-132-avoiders)
(critical moments of the largest jump); its sixth manuscript went to the
Fabius drafts tree.  Batch 65 added a Part IV to
[`open-query-membership-games`](ordinals-and-order-types/games-on-ordinals/open-query-membership-games)
(closure-word duality for fixed colorings); its other four manuscripts went
to the Fabius drafts tree and the Transseries tree.  Batch 66 added Parts II
and III to
[`constrained-crossover-closure`](automata-and-formal-languages/constrained-crossover-closure)
(PSPACE-complete finite stabilization for NFA input; decidable regularity of
the full closure), a Part III to
[`cigler-conjecture-16-parity`](hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity)
(cyclotomic pole collapse), a Part III to
[`insertion-degree-spectra`](automata-and-formal-languages/insertion-degree-spectra)
(sharp isolation thresholds) and a Part X to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(rare stable markings on random trees); its remaining manuscript went to the
Fabius drafts tree.  Batch 67 added Parts V and VI to
[`dfao-reversal-coloring-obstruction`](automata-and-formal-languages/dfao-reversal-coloring-obstruction)
(a near-linear threshold with theta limits; minimal recurrences and a
nineteen-output cancellation) and a Part II to
[`domination-root-minus-four-order-30`](graph-theory/domination-root-minus-four-order-30)
(cycle budgets for integer domination roots); its remaining manuscript went
to the Fabius drafts tree.  Batch 68 added a Part V to
[`open-query-membership-games`](ordinals-and-order-types/games-on-ordinals/open-query-membership-games)
(universal word profiles at every finite height), a Part XI to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(Hall bottlenecks for normalization by the matching number) and a Part VI to
[`adjacency-bounded-132-avoiders`](enumerative-combinatorics/adjacency-bounded-132-avoiders)
(a staircase of polynomial rarity below half size); its other three
manuscripts went to the Fabius drafts tree.  Batch 69 brought nothing to
this collection.  Batch 70 opened a fourth Jacobian-conjecture report,
[`keller-map-dynamical-degrees`](jacobian-conjecture/keller-map-dynamical-degrees)
(degree growth, shear spectra and arithmetic escape under iteration of the
three-variable counterexample), and added a Part IV to
[`cigler-conjecture-16-parity`](hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity)
(Cigler's Conjecture 17, proved in sign-corrected form), a second proof of
the depth-three classification to
[`power-tower-derivative-term-counts`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts)
(with a harmonic sign law), a Part III to
[`sextic-block-resolvent-separators`](galois-theory-and-radicals/sextic-block-resolvent-separators)
(the zero-parameter matching test) and a Part XII to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(rank-three ultra-log-concavity of matching supports); its sixth
manuscript went to the Fabius drafts tree.  Batch 71 added a Part IV to
[`constrained-crossover-closure`](automata-and-formal-languages/constrained-crossover-closure)
(quadratic finite rank for NFAs), a Part XIII to
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
(weighted rank three by leaf compression) and a Part VII to
[`adjacency-bounded-132-avoiders`](enumerative-combinatorics/adjacency-bounded-132-avoiders)
(the exact half-size crossover); its fourth manuscript went to the Fabius
drafts tree.

Batch 72, seventy-nine archives in one delivery, opened three reports:
[`power-tower-exponent-supports`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-exponent-supports)
(the leading asymptotic `N^2/2` of the derivative supports of `x^(x^a)` for
every integer `a`, hence for A293239 and A290268, from seven manuscripts),
[`a290268-unbounded-deficits`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a290268-unbounded-deficits)
(A290268 when the logarithmic deficit grows, from eight) and
[`matching-rank-normalization`](log-concavity-and-unimodality/matching-rank-normalization)
(twenty-seven manuscripts continuing Parts XI–XIII of
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes),
which gained dated pointers to it but no new Part). It added three
manuscripts on the Lehmer–Comtet triangle and two on depths five and six and
count bounds to
[`power-tower-derivative-term-counts`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts),
and a Part VIII (every fixed phase amplitude and reciprocal crossover) and a
Part IX (growing caps, from six manuscripts) to
[`adjacency-bounded-132-avoiders`](enumerative-combinatorics/adjacency-bounded-132-avoiders).
Twenty-one other manuscripts — thirteen on Thue–Morse pressure signs and
eight on Fabius observation masks — were filed in the Fabius drafts tree.
Vladimir asked for particular vigilance about duplicates in this batch.
Three archives repeated batch 71 byte for byte (the leaf-compression
manuscript printed as Part XIII of `preorder-root-polytopes`, the half-size
crossover printed as Part VII of `adjacency-bounded-132-avoiders`, and a
Fabius-tree note), one was a byte copy of another archive of the same batch,
and two were superseded (an earlier version of a Thue–Morse note, and an
A290268 note wholly implied by another); none of these six was placed.
Theorems proved by more than one manuscript are printed once, with the other
proofs kept as marked second routes: the integer-exponent asymptotic, for
instance, was proved three times.

Batch 73, sixty-two archives in seven arrival commits, opened sixteen
reports. Thirteen are single-sequence studies in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics):
[`a139217-greedy-dissociated-fringes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a139217-greedy-dissociated-fringes)
(finite fringes and closed forms for A139217 and A139218),
[`a022629-distinct-partition-norms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a022629-distinct-partition-norms)
(five Kotesovec conjectures, to all orders),
[`a097356-sqrt-restricted-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a097356-sqrt-restricted-partitions)
(three exceptions before every square),
[`a033552-catalan-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a033552-catalan-partitions),
[`a125054-central-poupard-numbers`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a125054-central-poupard-numbers)
(Bala's continued fraction and `a(n) ≡ 3 (mod 9)`),
[`a357825-theta-ballot-power-sums`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a357825-theta-ballot-power-sums),
[`a215561-fixed-composition-excursions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a215561-fixed-composition-excursions),
[`a279619-level-seven-gamma-constant`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279619-level-seven-gamma-constant),
[`a205497-zigzag-eulerian-spectra`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a205497-zigzag-eulerian-spectra),
[`a000382-winding-correction`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000382-winding-correction),
[`a330266-balanced-smirnov-poisson`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson)
(Kirgizov's `e^-(k-1)` conjecture),
[`a189281-path-forest-expansions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions)
and
[`a039831-two-fourier-peaks`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a039831-two-fourier-peaks)
(Kotesovec's `3(n/e)^n`). Two are in
[`congruences-and-valuations`](congruences-and-valuations):
[`a321941-asymptotic-coefficient-integrality`](congruences-and-valuations/a321941-asymptotic-coefficient-integrality)
(the Brent–Glasser–Guttmann integrality and mod-32 conjectures) and
[`a168362-lacunary-iterates-mod4`](congruences-and-valuations/iterated-series/a168362-lacunary-iterates-mod4).
The sixteenth,
[`preorder-gamma-rank-ulc`](log-concavity-and-unimodality/preorder-gamma-rank-ulc),
merges eleven manuscripts and a supplement from eighteen archives and answers
Research question 96 of
[`preorder-root-polytopes`](enumerative-combinatorics/preorder-root-polytopes)
for unit activities through actual degree four. The batch added Parts II to
[`apery-hankel-determinant-growth`](hankel-determinants/growth-and-runs/apery-hankel-determinant-growth)
(the limit of `h_n/Λ^(2n)`, so `D_n/D_(n-1) ~ KΛ^(2n)`),
[`binary-substitution-discrepancy`](generating-functions-and-asymptotics/binary-substitution-discrepancy)
(the family `0 → 1, 1 → 1 0^a 1^b`) and
[`a088714-bell-scale-growth`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth)
(golden-ratio moment laws); depths seven and eight to
[`power-tower-derivative-term-counts`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts),
whose open region is now deficit `m ≥ 9`; Parts V–VII to
[`constrained-crossover-closure`](automata-and-formal-languages/constrained-crossover-closure)
(rational rank slopes; coNP-complete stabilization for complete binary DFAs;
`F(s)/s² → 1`); and a Part V to
[`matching-rank-normalization`](log-concavity-and-unimodality/matching-rank-normalization)
(a nonreal zero at unit weights and matching number three needs fifteen
vertices; two-element Lorentzian deformations; three-tail obstructions). Of
its other manuscripts, one went to the Fabius drafts tree, one (A006014) to
`Analysis/Transseries`, and three became a new surreal report,
[`real-vector-space-structure`](../../../../Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/).

Vladimir again asked for vigilance about duplicates. Ten archives of
batch 73 were not placed: seven were superseded by archives that were (four
earlier editions, among them those of the DFA-crossover and common-path-rank
manuscripts; one special case contained in another archive; two earlier
versions of `preorder-gamma-rank-ulc` sources), and three were manuscripts that re-proved Part I of batch 72's
`matching-rank-normalization`. Four pairs proved the same theorems in
independent texts on the same day (A139217, A022629, A215561, A279619); each
pair is one report, its shared theorems printed once and the other proof kept
as a marked second route. The two depth-seven certificates are both kept, as
two proofs. Re-proofs of results already in the collection — Part I of the
Apéry Hankel and A088714 reports, the batch-72 power-tower certificates,
results of `preorder-root-polytopes` and `matching-rank-normalization` — are
printed as pointers, and the Lambert-W inversions many manuscripts re-derive
cite the transseries volume instead of claiming novelty.

Batch 74, five archives in one arrival commit, opened two reports:
[`a273821-first-pattern-failure`](enumerative-combinatorics/a273821-first-pattern-failure)
(the generating function marked conjectural in A273821, with a phase
transition at weight two) and
[`a238016-restricted-partitions-cubic-boundary`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a238016-restricted-partitions-cubic-boundary)
(`p_m(N) ~ N^(m-1)/(m!(m-1)!)` exactly when `N/m³ → ∞`). It added a Part II
to
[`factorial-ratio-polynomial-divisibility`](congruences-and-valuations/factorial-ratio-polynomial-divisibility)
(rational dilation, integrality and algebraicity for A347854–A347858 and
A295432) and to `a189281-path-forest-expansions` (shape-uniform fixed-gap
asymptotics), and a second derivation to `a097356-sqrt-restricted-partitions`.
Three of its five manuscripts overlapped reports placed hours earlier: the
A097356 and A189281 manuscripts re-proved those reports' theorems in
independent text with equal constants, and the fractional-factorial
manuscript re-proved Part I's A295431 theorem with weaker constants. Each
shared theorem is printed once, as the earlier report's, with the newcomer's
proof as a second route; only their own results were added. No archive of
batch 74 was superseded.

Batch 75, six archives in one arrival commit, opened three reports:
[`a069762-pyramidal-frobenius`](enumerative-combinatorics/a069762-pyramidal-frobenius)
(the exact Frobenius number of three consecutive square-pyramidal numbers,
a period-six quintic quasipolynomial with six exceptions),
[`valley-monotone-bargraphs`](enumerative-combinatorics/valley-monotone-bargraphs)
(Flórez–Ramírez–Villamizar's growth conjecture with certified constants, and
infinitely many real poles) and
[`a126764-lconvex-polyominoes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a126764-lconvex-polyominoes)
(the Guttmann–Kotěšovec asymptotic of A126764 with three corrections). It
added Sections 15–19 to `a022629-distinct-partition-norms` (sharp saddle
scales, eventual log-concavity and Jensen hyperbolicity, convolution powers)
and a Part IV to `a215561-fixed-composition-excursions` (a proof of
Kauers–Koutschan's Conjecture 15, the A215570 recurrence). Duplicates: the
two A022629 manuscripts are the third and fourth independent proofs of that
report's theorems, with identical coefficients, and about two thirds of the
A215570 manuscript re-proves results of the A215561 report's Parts I–II.
These re-proofs are listed in one table per report, not reprinted. No
archive of batch 75 was superseded.

Batch 76, seven archives in one arrival commit, opened two reports.
[`lexicographic-well-orderings-of-reals`](ordinals-and-order-types/lexicographic-well-orderings-of-reals)
merges three independent manuscripts on one question, the lexicographic
order of all well-orderings of the reals (size `2^𝔠`, universal for orders of
size `𝔠`, coding length and representation rank `𝔠⁺`, exact character and gap
spectra).
[`group-theoretic-substrates`](hilbert-tenth-problem/group-theoretic-substrates)
joins two manuscripts on groups as Diophantine substrates (quartics for van
Kampen area; three free abelian subgroups of a Heisenberg power with
c.e.-complete product membership); batch 78 added its Parts III–IV. Batch 76
also added a Part III to `a088714-bell-scale-growth` (`liminf (r_n −
n/W(n)) ≥ 3/2`, and a reduction of the finer Bell conjecture to one scalar
defect estimate) and a Part IX to
`probabilistic-quantum-and-continuous-computation` (stopping laws of rational
quantum loops). Duplicates: the three well-ordering manuscripts are
independent texts that prove the same core three times, and each answers a
question another leaves open; each shared theorem is printed once, with the
other proofs as second routes. One of them re-proves a corollary of
[`point-separating-game-values`](ordinals-and-order-types/games-on-ordinals/point-separating-game-values),
which now points back; the Bell manuscript re-derives Part I's conditional
reduction, and the quantum manuscript repeats three arguments of its host.
These are printed as pointers. Four files of the Bell archive equal
repository files and were not staged. No archive of batch 76 was
superseded.

Batch 77, seventy-one archives in one arrival commit, was placed in six
clusters and opened thirty-four reports. One is in
`automata-and-formal-languages`:
[`accessible-and-strong-automata`](automata-and-formal-languages/accessible-and-strong-automata)
(accessible and strongly connected automata to every fixed order). The other
thirty-three are single-sequence studies in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics):

- ascent sequences and a surjection diagonal (77P1):
  [`a202061-ascent-120-deficit`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202061-ascent-120-deficit)
  (the deficit `Θ(n^(1/3)(log n)^(2/3))` to every inverse-logarithmic order,
  from five chained manuscripts),
  [`a202058-ascent-000-growth`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202058-ascent-000-growth)
  (the factorial constant `8/(3π²)`),
  [`a202062-ascent-201-enumeration`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202062-ascent-201-enumeration)
  (the Guttmann–Kotěšovec cubic generating function) and
  [`a122399-surjection-diagonal`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a122399-surjection-diagonal);
- (77P2)
  [`a139383-iterated-bell-diagonals`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a139383-iterated-bell-diagonals)
  (Prellberg's 2002 formula has priority),
  [`a377922-corner-polyhedra-schnyder`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a377922-corner-polyhedra-schnyder)
  (Fusy–Narmanli–Schaeffer's Conjecture 25),
  [`a113227-powered-catalan`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113227-powered-catalan)
  (Elizalde's question on the pattern 1-23-4),
  [`a380274-mahonian-growing-powers`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a380274-mahonian-growing-powers),
  [`a301746-divisor-weighted-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301746-divisor-weighted-asymptotics)
  (Kotěšovec's A301746 conjecture, and A294363) and
  [`a294220-ascent-multiplicity-caps`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a294220-ascent-multiplicity-caps);
- trees, networks and automata of finite languages (77P3):
  [`a399421-galled-trees`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a399421-galled-trees)
  (three gall-count regimes),
  [`a082161-airy-amplitudes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a082161-airy-amplitudes)
  (positive Airy amplitudes for relaxed and compacted trees and minimal
  automata, every fixed arity; six manuscripts),
  [`a213863-tree-child-networks`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a213863-tree-child-networks),
  [`a333497-historic-trees`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a333497-historic-trees)
  (Burghart–Wagner's Conjecture 1 fails for every order `r ≥ 30`),
  [`a000651-takeuchi-numbers`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000651-takeuchi-numbers),
  [`a116379-bounded-identity-trees`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a116379-bounded-identity-trees)
  and
  [`a000571-tournament-score-sequences`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000571-tournament-score-sequences);
- words, permutations, partitions and placements (77P4):
  [`a239144-forbidden-distance-involutions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a239144-forbidden-distance-involutions),
  [`a260700-parabolic-double-cosets`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a260700-parabolic-double-cosets)
  (Browning's higher-order conjecture),
  [`a260952-full-support-signed-permutations`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a260952-full-support-signed-permutations),
  [`a227578-ordered-rook-paths`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a227578-ordered-rook-paths),
  [`a108242-regular-cyclic-word-covers`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a108242-regular-cyclic-word-covers),
  [`a301981-unitary-divisor-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301981-unitary-divisor-partitions)
  (the recorded OEIS equivalents of A301981 and A301982 are false),
  [`a174065-radix-layer-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a174065-radix-layer-partitions)
  (those of A174065 and A393565 omit a log-periodic factor),
  [`a372395-acyclic-orientation-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a372395-acyclic-orientation-partitions),
  [`a201513-sparse-chess-placements`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a201513-sparse-chess-placements)
  and
  [`a380592-tied-football-seasons`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a380592-tied-football-seasons);
- moments, renewals and moving parameters (77P5):
  [`a292507-binomial-partition-transform`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a292507-binomial-partition-transform),
  [`a113226-vincular-avoiders`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113226-vincular-avoiders)
  (Bevan–Cheon–Kitaev's Conjectures 13 and 14 with exact constants),
  [`a124380-signed-moment-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a124380-signed-moment-asymptotics),
  [`a047909-beta-renewal-subsequences`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a047909-beta-renewal-subsequences),
  [`cooper-level-15-moving-zeros`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/cooper-level-15-moving-zeros)
  (the constants of Cooper's Table 8) and
  [`a291698-moving-fugacity-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a291698-moving-fugacity-partitions).

It extended seven reports: Section 14 of `preorder-gamma-rank-ulc` (77U: the
five-vertex universal-sink cores are rank-ULC at every actual degree); a
Part III of `apery-hankel-determinant-growth` (full equivalents for
proportionally shifted determinants), Parts II of `a330266-balanced-smirnov-poisson`
(the uniform remainder Part I sketched) and `a126764-lconvex-polyominoes` (the
all-orders coefficient theorem), and a third route for
`a279619-level-seven-gamma-constant` (77P5); a fifth source for
`a022629-distinct-partition-norms` (slot multiplicities and Kotěšovec's
A266891 conjecture) and a Part V of `a215561-fixed-composition-excursions`
(the A215562 first correction) (77P2). Three 77P5 manuscripts on late
coefficients of divergent series went whole to `Analysis/Transseries`.

Vladimir asked again for vigilance about duplicates. Three archives of
batch 77 were superseded and nothing of them was placed: the first edition of
the iterated-Bell manuscript, which differs only in its credit to Prellberg;
the earlier release of the galled-tree crossover manuscript; and the
involution manuscript before its attribution revision. Several archives nest
their predecessors byte for byte — the A202061 chain of five, the A202058
chain, and the iterated-Bell, corner-polyhedra and powered-Catalan addenda —
and each paper was staged once; the 77U archive repeats 27 files and five
whole companion archives of batch 73, which were not staged again. Same
theorems: the A022629 manuscript is a fifth independent proof of that
report's theorems, the A215561 manuscript a fourth proof of its main
theorems, the level-seven manuscript a third proof of the A279619 constant,
the second L-convex manuscript re-proves Part I's three corrections, and the
shifted Apéry manuscript re-proves Part I's linear-shift law; these are
tabulated or printed as routes, not reprinted as new results. Inside the
batch, the two forbidden-distance manuscripts share the case `r = 1` with
the same coefficients, the ternary Airy manuscript is the `k = 3` case and
base proof of the fixed-arity one, the finite-language automaton manuscript
repeats a compacted-tree manuscript's appendix, and a later A202061 paper
restates Part I; each shared result is printed once. Heavy regenerable
artifacts were excluded with rebuild recipes in the report READMEs: 18 page
renders of the A202058 chain, five galled-triangle files and two
exact-value tables of the A113226 report. The five-core certificate shards
of `preorder-gamma-rank-ulc` (95.1 MB) cannot be regenerated by any shipped
program; they stay in the arrival commit, and that report's README says how
to retrieve and replay them.

Batch 78, fourteen archives in four arrival commits, opened three reports in
[`hilbert-tenth-problem`](hilbert-tenth-problem):
[`signal-machine-collision-certificates`](hilbert-tenth-problem/signal-machine-collision-certificates)
(degree-two sums of squares with one witness per realization of a collision
history),
[`stochastic-and-thermal-exactness`](hilbert-tenth-problem/stochastic-and-thermal-exactness)
(undecidable exact events in uniformly convergent stochastic and thermal
systems) and
[`quadratic-orthant-certificates`](hilbert-tenth-problem/quadratic-orthant-certificates)
(degree-two orthant certificates for maximal parallel rounds, timed races and
a fixed Waterfall universal machine). It added Parts XV and XVI to
`canonical-diophantine-certificates` (interaction-combinator wiring with a
sharp `2/5`–`2/3` loop-parity separation; sandpile odometer certificates
without toppling histories) and Parts III–IV to `group-theoretic-substrates`
(pair counts in Heisenberg words; affine inputs to subgroup membership).
Duplicates: the two signal-machine manuscripts prove one theorem by two
routes, both printed; two of the three interaction-combinator manuscripts
prove one compiler theorem by one method, which is stated once; results of
`canonical-diophantine-certificates` Parts V and XI that several manuscripts
re-prove are printed as pointers; and the Waterfall manuscript rediscovers an
erratum in the Neary–Woods machine table that the Hilbert's-tenth research
tree had already found. No archive of batch 78 was superseded. Two
certificate files of the stochastic-game manuscript (11.9 and 21.8 MB) are
regenerated by its own program and not shipped. The two Waterfall
machine-data files of `quadratic-orthant-certificates` are third-party data with no upstream licence
observed, staged with a provenance note and not covered by the repository's
MIT-0 licence.

Batch 79, nineteen archives in four arrival commits, was placed in three
clusters and opened two reports in
[`hilbert-tenth-problem`](hilbert-tenth-problem):
[`polynomial-witness-histories`](hilbert-tenth-problem/polynomial-witness-histories)
(unique linear certificates whose unknowns are a fixed number of finite
polynomials over ℕ[X,Y], ℕ[X] or any commutative ring, from three
manuscripts, the second answering the first's question on one coordinate)
and
[`smooth-diophantine-finalizers`](hilbert-tenth-problem/smooth-diophantine-finalizers)
(five more variables turn any quadratic certificate into a quartic that is
smooth over ℤ, with the same natural zeros). It extended five reports:
`canonical-diophantine-certificates` gained Parts XVII–XIX (sign charts of
exponential trajectories with power atoms and the order-two power boundary;
grammar-compressed queue traces; eager Tree Calculus with a literal universal
tree) and a second route inside Part XVI, and now prints twenty-one
manuscripts in 605 pages; `stochastic-and-thermal-exactness` gained Parts
IV–V (positive mixing realizations of polynomials; coercive Green
operators), `liveness-beyond-halting` Part VI (least clock degrees),
`signal-machine-collision-certificates` Parts III–IV (a conservative
universal signal machine; sparse lattice certificates) and
`quadratic-orthant-certificates` Parts IV–VI (active membranes; reset Petri
nets). `probabilistic-quantum-and-continuous-computation` gained a dated note
on the smooth finalizer. Duplicates: one archive was superseded and nothing
of it was placed, the first edition of the conservative-signal manuscript,
whose corrected edition (the same text with the research tree's repair)
arrived later the same day. The two exponential sign-chart manuscripts prove
one theorem by two routes, and so do the two coercive-operator manuscripts;
both routes are printed. The second sandpile manuscript re-proves Part XVI of
`canonical-diophantine-certificates` independently, with quadratic residuals
instead of cubics (neither ledger improves the other), and is printed inside
that Part as a marked second route. The reset-net manuscript re-derives the
universal-membrane manuscript's program layer without citing it (its program
files are byte-identical), which is printed once; the two membrane
manuscripts are complementary. Results of `canonical-diophantine-certificates`
(among them Parts I, II, V, VI, IX, XI and XIII), `liveness-beyond-halting`,
`signal-machine-collision-certificates` Part I and
`stochastic-and-thermal-exactness` Part I that the manuscripts re-prove are
printed as pointers or marked second routes. Heavy regenerable artifacts were
excluded with rebuild recipes in the report READMEs: three expanded-polynomial
exports of `polynomial-witness-histories` (3.7 MB) and twenty-one schema,
trace and fixture files of `signal-machine-collision-certificates` and
`quadratic-orthant-certificates` (70.1 MB), each regenerated at placement and
compared byte for byte up to line endings (the compressed ones after
decompression). The Hilbert's-tenth research tree,
maintained by another session, reviewed all nineteen archives, most of them
before placement, authenticated the three placements against the archives and
audited the written Parts; the report READMEs link those reviews, and the
shipped programs are the delivered bytes, with the tree's patches not
applied. No manuscript refutes a repository claim.

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
so rather than let a shared setup suggest the answers are connected.  Two
later reports sit beside it rather than inside it:
[`power-tower-exponent-supports`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-exponent-supports)
proves the leading constant `1/2` for `x^x` and `x^(x^2)` that the article
leaves open, and
[`a290268-unbounded-deficits`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a290268-unbounded-deficits)
studies the `x^(x^2)` coefficients at unbounded logarithmic deficit.

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
