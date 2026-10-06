<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

Two hundred and thirty-nine independent mathematical research packages, unpacked
from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all two hundred and thirty-nine reports, names the problem each one attacks
and the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites and their Booleanizations, ideals, lattice congruences, lexicographic orders of the well-orderings of the reals, measurable box games and hat guessing, named elementary embeddings in urelement set theory, random bits and cuts of models of arithmetic, noisy parity on cubes, robust neutral choice, Freiling symmetry from finite blacklists, bounded-width power-set compression | 27 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, preorder and order polytopes, numerical semigroups, lattice arrays, tropical degree, mesh patterns, skew partitions, polyomino growth, first pattern failures, pyramidal Frobenius numbers, valley-monotone bargraphs, bridgeless toroidal maps | 26 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, Cigler's conjectures, growth and runs, arithmetic numerators | 10 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems, MDS codes, binomial decompositions, Bernoulli entropy, matching-rank normalization, preorder gamma polynomials | 14 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, Apéry and Motzkin congruences, iterated series, integrality of asymptotic coefficients, valuations and periodicity | 11 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy, single-sequence OEIS studies (power-tower derivative supports, restricted and weighted partitions, excursions and restricted permutations, Fourier peaks, gamma constants, L-convex polyominoes, pattern-avoiding ascent sequences, iterated Bell diagonals, corner polyhedra, powered Catalan and Mahonian numbers, divisor-weighted products, phylogenetic trees and networks, Airy amplitudes of trees and automata, historic and identity trees, Takeuchi numbers, tournament scores, involutions, parabolic cosets and signed permutations, rook paths, cyclic word covers, colored and radix-layer partitions, acyclic orientations, chess placements, football seasons, vincular avoiders, Beta renewals, signed moments, moving zeros and fugacities, rounding extinction, matrix compositions, extensional acyclic digraphs, long increasing subsequences, shifted rectangles, clipping tables, stable Hilbert series, bipartite and leafless multigraphs, strict twice partitions, column-convex permutominoes, self-modified and weak ascent sequences, one-sided rectangulations, Tesler matrices, closed lambda terms, self-complementary tournament scores, inversion-sequence classes, diagonally symmetric alternating sign matrices, unique pattern occurrences, a weighted Dyck Newton diagonal, a proportional placement game, alternating Baxter involutions, circle, permutation and interval graphs, diagonal and iterated Euler transforms, strict partition chains, sub- and superdiagonal partitions, Stirling products and transforms, disjoint partition families, odious and evil partitions, pop-stacked permutations, bounded-indegree DAGs, nested cycle assemblies, constrained 0-1 and integer matrices), Apéry arrays | 115 |
| [`automata-and-formal-languages/`](automata-and-formal-languages) — shuffle state complexity, DFAO reversal, synchronization, language hierarchies, additive complexity, counting accessible and strongly connected automata | 8 |
| [`quaternionic-analysis/`](quaternionic-analysis) — slice regularity, Cauchy–Fueter analysis, the global inverse Fueter problem | 1 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`jacobian-conjecture/`](jacobian-conjecture) — fibers and dynamics of Keller maps: Gao's five-dimensional map, arithmetic fibers, weighted rigidity and dynamical degrees of the three-variable counterexample | 4 |
| [`galois-theory-and-radicals/`](galois-theory-and-radicals) — bad characteristics of radical solvers, Fourier–Kummer charts, finite separating ranges for sextic resolvents | 2 |
| [`hilbert-tenth-problem/`](hilbert-tenth-problem) — witness-faithful Diophantine certificates for discrete computation; Diophantine laws of probabilistic, quantum and continuous computation; recurrence and liveness beyond halting; groups as Diophantine substrates; signal-machine collision certificates; exact events in stochastic and thermal systems; quadratic orthant certificates; polynomial witness histories; smooth Diophantine finalizers; five-particle binary automata; fixed universal polynomials; periodic turmites and a literal Langton ant | 12 |
| **Total** | **239** |

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
(the Brent–Glasser–Guttmann integrality and mod-32 conjectures; batch 86
added a Part II proving their negativity conjecture `r_k < 0` and the law
`r_k ~ −16^k (k!)²/(π^(3/2) k^(3/2))`) and
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
  (Burghart–Wagner's Conjecture 1 fails for every order `r ≥ 30`; A333497 and A336009 are not P-recursive; four manuscripts),
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
  (the recorded OEIS equivalents of A301981 and A301982 are false; batch
  86's Part II: the ratios have liminf 0 and limsup infinity),
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
(unique certificates whose unknowns are a fixed number of finite
polynomials: affine-linear over ℕ[X,Y] or a nonzero commutative ring, and
quadratic over ℕ[X] with a shared stride, from three manuscripts, the
second answering the first's question on one coordinate)
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

Batch 80, twelve archives in one arrival commit, was placed in three
clusters and opened no report in this collection; its third cluster became
the surreal collection's new report
[`surreal-well-orders`](../../../../Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders).
Three archives are their authors' corrected code editions of batch-79
packages: each repairs the input-domain defect that the Hilbert's-tenth
research tree's review found in the shipped Python of
`canonical-diophantine-certificates` Part XIX,
`quadratic-orthant-certificates` Part VI and
`signal-machine-collision-certificates` Part IV, with a guard equivalent to
the review's patch and a new regression test. Their manuscripts are
byte-identical to batch 79, so nothing printed changed; the corrected files
supersede the batch-79 code and replace it under the same names (the old
bytes stay in the placement commit). Four further manuscripts became Parts
V–VI of
[`signal-machine-collision-certificates`](hilbert-tenth-problem/signal-machine-collision-certificates)
(conserved-mass thresholds): with many weight-one symbols, a universal
reversible two-counter machine compiles to one fixed reversible cellular
automaton at conserved mass three, so three units suffice for undecidable
pattern occurrence, and, by inverse execution, for exact-pair reachability;
with a single unit symbol, masses three and four stay decidable, so
integer-state number-conserving automata need at least five particles.
Duplicates (Vladimir asked to watch for them): one archive,
`Single_Unit_Three_Mass_Decidability.zip`, is superseded by its attribution
revision (the "(1)" copy, which credits earlier work and changes no
mathematics, program or receipt), and nothing of it was placed. The
three-mass manuscript re-proves the report's mass-two theorem
(`smc:sl:thm:two`, Part IV) by the same argument, printed as a pointer, and
its receipt is a byte-identical copy of Part IV's, not staged again; the
exact-target manuscript is a declared extension of it whose five vendored
programs are byte-identical to its own and are shipped once; the
single-unit manuscript reruns Part IV's semilinearity architecture one mass
higher, and the four-mass manuscript restates the single-unit ingredients,
both marked with pointers. The four surreal manuscripts are independent
texts, although two pairs share an archive name: none supersedes another.
The core they prove up to four times (universality of `No`, the
global-choice equivalence, interpolating cores, diagonal non-coding,
binary-class equimorphism, inaccessible models) is printed there once, with
the other proofs as routes or notes, and their set-sized layer, which
re-proves
[`lexicographic-well-orderings-of-reals`](ordinals-and-order-types/lexicographic-well-orderings-of-reals),
is printed as pointers to it; that report gained a dated note, because one
of the surreal manuscripts answers its question "Other ground orders" in
part. Five rule and certificate exports of the three-mass manuscript
(20.8 MB) were excluded with a rebuild recipe. The Hilbert's-tenth research
tree reviewed all twelve archives before the writes, authenticated the
placements and audited the written texts; its README patch for the three
corrected-code Parts was applied in `7969f7168`. No manuscript refutes a
repository claim.

Batch 81, six archives in two arrival commits, brought nothing to this
collection: all six continue the surreal collection's
[`surreal-well-orders`](../../../../Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders),
as its Parts VI–IX. One of them answers part of the question "Other ground
orders" of
[`lexicographic-well-orderings-of-reals`](ordinals-and-order-types/lexicographic-well-orderings-of-reals),
which gained a dated note.

Batch 82, twenty-three archives in one arrival commit, all "Research
Reports" of one AI-assisted research pipeline built on the Hilbert's-tenth
programme's research tree, was placed in four clusters in
[`hilbert-tenth-problem`](hilbert-tenth-problem). It opened two reports:
[`five-particle-binary-automata`](hilbert-tenth-problem/five-particle-binary-automata)
(ten Reports on one globally reversible, number-conserving binary cellular
automaton: five particles are the exact threshold for binary and for
reversible binary rules, a literal universal reversible source, startup and
cellular clocks, an exact lazy evaluator, quartic certificates and a
parallel two-involution replacement rule) and
[`fixed-universal-polynomials`](hilbert-tenth-problem/fixed-universal-polynomials)
(five Reports on the programme's own fixed universal polynomial: a literal
Grill instance of exact degree 69,339,973, the exact degree law `87N + 16`
behind it, the entire native witness fiber with a `ζ(1/2)` second term, and
the failure of positive index restoration with a counting law for its
counterexamples). It added a third source to Part VI and Parts VII and VIII
to
[`signal-machine-collision-certificates`](hilbert-tenth-problem/signal-machine-collision-certificates)
(fixed-input timed quartics; mass-four decidability in every dimension,
orbit geometry and a binary planar shuttle; horizon-free certificates for
exact three-mass targets with infinite native fibres) and a Part V to
[`group-theoretic-substrates`](hilbert-tenth-problem/group-theoretic-substrates)
(229 literal `SL_4(ℤ)` matrices whose positive semigroup simulates the
Neary–Woods machine, with bounded-length certificates). Duplicates (Vladimir
asked to watch for them): the first edition of Report 23 is superseded by
its revision, which anchors it, and nothing of it was placed; Reports 25 and
33 were re-shipped as context of Report 34, and several archives re-ship
whole earlier Reports or repository files, staged once or cited by path.
Report 15 implies Report 14's threshold (both printed, Report 14 keeping its
literal instance); Report 22's infinitude theorem is implied by Report 25,
and Report 29 proves the signal-machine report's mass-four theorem again in
dimension one; Report 27 restates a lemma of Report 26. Re-derivations of
`quadratic-orthant-certificates`, `canonical-diophantine-certificates`, the
signal-machine report and research-tree constructions are printed as
pointers or credited second routes. Heavy regenerable files (the Report 16
and 17 tables, 174 MB; a 32 MB universal source; 70 emitted circuit files;
Report 23's 61 MB circuit DAG; Report 32's two certificate exports) were excluded with
rebuild recipes, and two third-party papers shipped by Report 23 are not
redistributed. No manuscript refutes a repository claim. Batches 81 and 82
were placed by an intake session that ended with their writes unfinished:
it committed Parts VI–VIII of the batch-81 addition and the first writes of
`five-particle-binary-automata` (Parts I–IV) and
`fixed-universal-polynomials` (Parts I–IV); the next session wrote the
rest, from its dossiers.

Batch 83, sixteen archives in six arrival commits, brought four of the
pipeline's Reports here (cluster H) and twelve surreal well-order
manuscripts to the surreal collection (Parts X–XIV of
`surreal-well-orders`). Reports 35 and 36 became Part XX of
[`canonical-diophantine-certificates`](hilbert-tenth-problem/canonical-diophantine-certificates)
(a literal periodic sandpile loader for the Neary–Woods machine on `ℤ³`, and
binary prism certificates whose nonnegative real zeros are all natural),
Report 37 Part V of
[`fixed-universal-polynomials`](hilbert-tenth-problem/fixed-universal-polynomials)
(an exact predicate for a positive zero with negative restored index; its
existence stays open), and Report 38 the new report
[`periodic-turmite-first-revisits`](hilbert-tenth-problem/periodic-turmite-first-revisits)
(first revisits of finite-defect periodic turmites in polynomial bit time,
exact first hits of finite observations, and no reduction of an undecidable
language through globally one-visit runs). Duplicates: Report 36 re-proves
Report 35's certificate theorem (printed once) and ships its composition
files; Report 35's certificate re-derives Part XVI's, and its machine table
equals one already in `quadratic-orthant-certificates`. The Hilbert's-tenth
research tree reviewed all four Reports before placement; the writes print
its findings. No manuscript refutes a repository claim.

Batch 84, seven archives, brought nothing here: all seven became the
surreal collection's new report
[`surreal-self-embeddings`](../../../../Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings).

Batch 85, nine archives in three arrival commits, was placed in three
clusters and opened five reports in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics):
[`a082528-rounding-extinction`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a082528-rounding-extinction)
(Cloitre's conjecture: repeated rounding down to multiples of `k^m` dies at
`(m Γ(m/(m+1))^(m+1) n)^(1/(m+1))`, every real `m > 0`),
[`a261781-matrix-compositions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions)
(exact minimal recurrences, Hankel products and uniform asymptotics for
A261781 and A261784, from two manuscripts),
[`a182220-source-boundary`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a182220-source-boundary)
(extensional acyclic digraphs: `A182220(n) = n − ⌈log₂ n⌉`, its upper half
Tomescu's, and the boundary diagonals of A182162),
[`a047874-long-increasing-subsequences`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a047874-long-increasing-subsequences)
(D-finiteness of the LIS arrays in every fixed sector, Kauers and Wang's
question, and five corrections for A269021) and
[`a181199-shifted-rectangles`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles)
(Kotěšovec's A181199 asymptotic, all-order expansions and an algebraicity
dichotomy). It added a Part III to `a189281-path-forest-expansions` (the
rational-collapse conjecture proved for every order, and integer correction
polynomials for every directed offset pair) and a Part II to
`a000571-tournament-score-sequences` (at coexistence the score sequence is
a logistic mixture of a giant-block phase and a many-block phase). Its
ninth manuscript, an exact inversion of the partition function (A306631),
went whole to `Analysis/Transseries` as that tree's thirteenth delivery.
Duplicates: the two matrix-composition manuscripts prove the same core
theorems independently on the same day and permute their Greek letters, so
they are one report in one notation with a dictionary, the second's
re-proofs tabulated; one of them claimed to prove two posted conjectures,
but the recurrence is Munarini, Poneti and Rinaldi's (2009) and only its
minimality is new. The A189281 manuscript repeats special cases of Part II
without credit, and the tournament manuscript re-proves Part I's
coexistence theorem; both are printed as notes. No archive was
superseded, and no manuscript refutes a repository claim. Reciprocal notes
went to four neighbouring reports (`ac33f7ac5`).

Batch 86, ten archives in three arrival commits, split two multi-subject
OEIS manuscripts by subject. They opened
[`a343093-bridgeless-toroidal-maps`](enumerative-combinatorics/a343093-bridgeless-toroidal-maps)
(a proof of Bala's square-convolution conjecture for rooted bridgeless
toroidal maps, with a three-term asymptotic) and added Parts IV and V to
[`a088714-bell-scale-growth`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth)
(positive real-analytic densities with full support, a nonzero
antiperiodic correction profile for the golden-ratio laws and every
fixed-shift expansion of A088713; and a proof of the finer Bell
conjecture, `a_n ~ C_* B_n exp(W(n)² + 3W(n))`, not yet independently
reviewed), a Part II to `a301981-unitary-divisor-partitions` (both one-sided
divergences occur: the ratios to the refuted models have liminf 0 and
limsup infinity) and a Part II to `a321941-asymptotic-coefficient-integrality`
(the negativity conjecture `r_k < 0` and the large-order law). Duplicates:
the two manuscripts prove the A088713 companion expansion independently
(the more general proof is printed, the other as a second route), and the
first, written without the second, still calls the Bell conjecture open.
The other eight archives, on Glazer's Question 2 and Polish models of
Presburger arithmetic, went to the surreal collection (the new report
`polish-models-of-omnific-arithmetic` and an addition to
`discrete-initial-subgroups-and-omnific-normalization`). No manuscript
refutes a repository claim.

Batch 87, six archives in one arrival commit, opened one report here:
[`measurable-box-games`](ordinals-and-order-types/measurable-box-games)
(Glazer's choiceless box-game paradox: exact minimax `⌊m/q⌋` for blind
cylinder-measurable outputs, a fair measure extension for countable teams,
executable maps as recursively sliceable cube matchings, the counts
`F_n = 1, 2, 9, 232, 206065, …` with an all-orders asymptotic expansion,
and a conditional Busy Beaver comparison; Glazer's question itself is
answered only for that class). It is the collection's first report on
box, hat or guessing games. The other five archives, on Baire-category
rigidity, nonsplit models, a claimed ATR₀ answer to Glazer's Question 1 of
the Topological Tennenbaum paper and locally compact cones, became Parts
VI–IX of the surreal collection's `polish-models-of-omnific-arithmetic`;
the box-game report's Q1 is a different question. Nothing was superseded,
and no manuscript refutes a repository claim; two provenance files naming
a third party's personal profile URL were not staged.

Batch 88, ten archives in one arrival commit, all "Research Reports"
39–48 of the Hilbert's-tenth programme's pipeline, was placed in two
clusters that share no theorem. Reports 40, 42, 44, 47 and 48 became Parts
II–IV of
[`periodic-turmite-first-revisits`](hilbert-tenth-problem/periodic-turmite-first-revisits)
and answer its question 3: a literal periodic Langton ant simulating the
fixed Neary–Woods machine U15 with at most two visits per cell, a fixed
polynomial initializing its board from two sentinel integers, and one fixed
polynomial with 465 positive witnesses and exact degree 2,304,000
recognizing U15's sentinel-pair halting language, rebuilt from the
literals 1 and 3 in 14,658,934 operations. It is not an ordinary-input
universal polynomial and leaves the programme's 84-operation record
unchanged; seven primitive cell maps derived from a third-party paper's
figure sources are credited and not covered by MIT-0. Reports 39, 41, 43,
45 and 46 became Parts VI–VIII of
[`fixed-universal-polynomials`](hilbert-tenth-problem/fixed-universal-polynomials)
(nonredundant main comparisons, the failure of first-index deletion, and
the free-coefficient 83 and square/product 82 candidates below the
record, with a table of every such candidate). Report 44 is a recovered
edition rebuilt after a filesystem reset, Report 45's main theorem is a
second route to a research-tree theorem, and Report 46 ships Report 45
whole; byte copies were staged once and 27 heavy regenerable files of
about 156 MB were excluded with recipes. Reciprocal notes went to
[`canonical-diophantine-certificates`](hilbert-tenth-problem/canonical-diophantine-certificates)
(Part XX) and between the two reports (`f7ca8360b`). No manuscript
refutes a repository claim.

Batch 89, five archives in two arrival commits, opened
[`naming-elementary-embeddings`](ordinals-and-order-types/naming-elementary-embeddings)
(Yao's urelement kernel models after finitely many canonical elementary
atom lifts are named: for `κ > ω`, Replacement holds exactly when the union
of small component-type blocks has fewer than `κ` atoms; for `κ = ω`,
every component and that union must be finite. Every one-name expansion preserves
Replacement iff `cf κ > ω`, and every expansion by two or more names iff
`cf κ > 2^ℵ₀`; a CH characterization at `ℵ₂`, and exact Collection and
reflection criteria). It contains no surreal mathematics and continues the
formal projects `SetTheory/ZF` and `SetTheory/BoundedConsistency`
semantically, without formalizing anything. Its Collection spectrum is
proved independently in Part VI of the surreal report
`birthday-cutoffs-and-hereditary-sets`, printed there with its own proofs.
The other four archives went to the surreal collection
(`surreal-well-orders` Part XV, `polish-models-of-omnific-arithmetic`
Part X, `birthday-cutoffs-and-hereditary-sets` Parts VI–VII). Nothing was
superseded, and no manuscript refutes a repository claim.

Batch 90, six archives in one arrival commit, added Part II to
[`measurable-box-games`](ordinals-and-order-types/measurable-box-games)
(Eldredge's infinite binary hat game: a computable strategy with surplus
`log₂ n + O(1)` almost surely and, for each positive `g = o(n)`, a continuous
finite-information strategy with surplus divided by `g` tending to infinity
almost surely, answering both questions of his Remark 6.8; the arbitrary-`g`
strategy need not be computable. Its finite corollary settles Part I's
question Q9 for one family). Part VIII of the surreal report `birthday-cutoffs-and-hereditary-sets`
(named symmetries) has, for finitely many named permutations, the `κ = ω`
case of `naming-elementary-embeddings`' component criterion as a case of
its orbit criterion for named group actions, proved independently; both
reports carry dated cross-references. The other five
archives went to the surreal collection: Parts XI–XII of
`polish-models-of-omnific-arithmetic`, a fourth source of
`discrete-initial-subgroups-and-omnific-normalization`, Part VIII of
`birthday-cutoffs-and-hereditary-sets` and the new report
`cantor-families-of-surreal-subfields`. Nothing was superseded, and no
manuscript refutes a repository claim. Reciprocal notes for batches 87, 89
and 90 are in `8d7d03c3e`, `fc1ad4275` and `e50dde15b`.

Batch 91, twenty-four archives of one arrival commit (`0d7f51c44`), was
the Hilbert's-tenth programme pipeline's Research Reports 49–71 (Report 68
was never delivered; only its README survives) and one OEIS pair, placed
by host in four commits. Reports 50 and 52–54 (`b0a536b63`, written in
`fb2287290`) became Part XXI of
[`canonical-diophantine-certificates`](hilbert-tenth-problem/canonical-diophantine-certificates):
fixed-arity positive-integer sandpile polynomials of exact degree 18 on one
raw input, which answer Part XX's packing question; Report 52 ships Report
50 whole, staged once, and six passages of Cairns's paper that two of them
call misprints were checked, each printed form failing. Fifteen Reports
(49, 51, 56–67, 69; `d750d98dd`, `61c9e3eb2`) became Parts IX–XIII of
[`signal-machine-collision-certificates`](hilbert-tenth-problem/signal-machine-collision-certificates):
a reversible four-particle timing threshold, periodic and five-signal
validity certificates, planar and projective returns, five-signal branching
and exact clocks, and native-gap compilers; the write corrected Report 64's
strict bound `25D/18 < T < 25D/9`, attained at `a = 1`, and Report 67's
nine heavy evidence files (about 35 MB) are rebuilt by recipe. Report 55
(`22a8ca89e`, `b93c4a0b5`) became Part VI of
[`group-theoretic-substrates`](hilbert-tenth-problem/group-theoretic-substrates)
(a degree-12 chronological matrix certificate with 184,016 gates and 41,309
witnesses), and Reports 70–71 (`22a8ca89e`, `4cabe3899`) Part VII of
[`five-particle-binary-automata`](hilbert-tenth-problem/five-particle-binary-automata)
(smaller sufficient recognition radii, answering Report 26's first
question). The OEIS pair (`ec8ae3dc7`, `9f924ac47`) opened the report
described in the next paragraph. Reciprocal notes are in `1fdcaf5a6` and,
for the signal-machine report, in its write. The Hilbert's-tenth research
tree reviewed the archives before placement (`49b100cfd`, `a9ab9a698`,
`bc6e1a62c`) and every publication after it (`316148ed5`, `f135cfb15`,
`4187c07d3`, `e92064458`, `5b9101184`, and `c529380eb` on the reciprocal
notes); `5b9101184` corrected summaries that could be read as one scalar
witness, and `c529380eb` refuted, retaining them, four summaries that
omitted the power theorem shared, with the containment lemma, by the
sandpile and matrix Parts. Nothing was superseded, no manuscript refutes a repository claim,
and the programme's 84-operation record is unchanged.

The batch-91 report
[`a196460-clipping-tables`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196460-clipping-tables/)
combines two manuscripts: the exact zero-versus-one positive-auxiliary
classification for each fixed finite two-coordinate clipping table and fixed-order
asymptotic, logarithmic and inverse expansions for A196460; then uniform
bounds for every truncation of its exact finite sector expansion. The latter
do not make the logarithmic or inverse expansions uniform in growing order.
Coefficients and degree may depend on the whole table; no uniform paid
integer compiler is supplied. The publication review of `9f924ac47`
(`e92064458`) checked
integration and these scope distinctions, not every analytic proof. It is
unrefereed and not formalized.

Batch 92, six archives in two arrival commits (`9dc8db274`, `afd7ffabb`),
added Parts III and IV to
[`measurable-box-games`](ordinals-and-order-types/measurable-box-games)
(`e38f368c2`, written in `721cf8196`): adaptive box games beyond cylinder
measurability, answering Part I's Q5 and Q2 for Borel and universally
measurable outputs (the Baire-property clause stays open), and the exact
expected-query threshold 2 for a divergent hat-guessing surplus, from two
independent manuscripts proving the same answer by the same construction,
merged with the more general one as base; the other settles Q9 for a larger
family. The write refuted, retaining it, the batch-90 sentence that every
other case of Q9 was open (Remark 15.1); the publication review
`42b49fdbd` refuted, retaining it, the write's own sentence that every
`q ≥ 3` case above `⌊m/q⌋` was open (Remark 15.2). Reciprocal notes went
to `non-baire-translation-invariant-ideal` and
`open-query-membership-games` (`9bffd43d5`). The other three archives
became Parts XIII–XV of the surreal report
`polish-models-of-omnific-arithmetic` (`e24ce2ce0`, `4af6f191d`), whose
Part XV shows a lemma of a Kuhlmann–Serra preprint false as stated. Nothing
was superseded, and no manuscript refutes a repository claim.

Batch 93, six archives in two arrival commits (`2faa3b37a`, `de37a66d1`),
added Part II to
[`naming-elementary-embeddings`](ordinals-and-order-types/naming-elementary-embeddings)
(`47a77daba`, written in `8a7f289b8`): commuting named actions, answering
its Question 10.4 in full, Question 10.1 for commuting permutations and
the fixed-action part of Question 10.10. Part VIII of the surreal report
`birthday-cutoffs-and-hereditary-sets` is credited as prior at `κ = ω`, and
one imported group-existence theorem is kept as an open check (Question
23.13). The other five archives went to the surreal collection: Parts II–III
of `definable-surreals-and-omnific-integers` and Parts XVI–XVII of
`polish-models-of-omnific-arithmetic`. The reciprocal notes on Part II went
to the birthday-cutoff report with its batch-95 write (`abba38172`); those
on the surreal Parts are in `c70ced0dd`. The Hilbert's-tenth tree reviewed
the publication of Part II (`c3da7b57a`) and found no defect within its
scope. Nothing was superseded, and no manuscript refutes a repository
claim.

Batches 94 and 95 brought nothing here. Batch 94's five complex-transseries
articles were filed whole under `Analysis/Transseries` as its fourteenth
delivery (`ec91f8c7c`, `6132faa30`); one of them refutes the directional
clause of a conjecture of the q-Pochhammer monograph there, corrected in
`7389d7de4`. Of batch 95's four archives, two became Part IX of the surreal
report `birthday-cutoffs-and-hereditary-sets` (`350b9a954`, `abba38172`)
and two the fifteenth transseries delivery (`05304d5ec`).

Batch 96, eleven archives in six arrival commits (`62846e17a`,
`7be14aa84`, `fb9f5884b`, `26e036956`, `78528873b`, `e3839ad2c`), was
placed in four clusters, two of them here. 96B added Part V to
[`measurable-box-games`](ordinals-and-order-types/measurable-box-games)
(`635a3e026`, written in `a21208b3f`): exact randomness thresholds for a
divergent hat-guessing surplus. With independent private coins, or a public
seed that is almost surely finitely valued, the admissible uniform expected
inspection caps are `(1, ∞)` (at cap 1 private coins succeed with
probability at most `1 − 1/5184`); one shared random integer of countably
infinite support attains cap 1 with every individual cost below 1. This
answers Part IV's Research question 57.2 except its private
positive-probability clause. The write refuted, retaining it, the
manuscript's hypothesis "finite positive-probability support" for its
finite-public theorem (Remark 75.6: a seed with one atom and a diffuse part
permits the endpoint), corrected one sentence of its abstract, and added
Corollaries 75.7–75.8 (prescribed seeds; caps conditional on the seed); the
Hilbert's-tenth publication review `47ab39154` refuted, retaining them, two
sentences of the write itself (Remark 75.9: the guide's extension of the
`1/5184` gap to finite public seeds, and an equality in the proof of
Corollary 75.7). 96C added Part III to
[`naming-elementary-embeddings`](ordinals-and-order-types/naming-elementary-embeddings)
(`27f200305`, written in `03683e579`): two independent manuscripts on
relations among named injections, both answering Part II's Question 23.3
with the same theorem, merged with `atom_actions_research` as base. For a
finitely generated commutative monoid acting by injections the connected
types number `|Sub(G)|`, `ℵ₀` or `2^ℵ₀` according to the rank `d`, with the
Replacement thresholds none, `cf κ > ℵ₀` and `cf κ > 2^ℵ₀`; Questions
23.1–23.2 and Part I's 10.1 are answered only with pure real parameters,
and the second manuscript's "commutative answer" to Question 23.5 was
narrowed to the monoid analogue. The other eight archives went to the
surreal collection: four on Borel conjugacy, support complexity, Borel
flows and pairs of derivations became Parts XVIII–XXI of
`polish-models-of-omnific-arithmetic` (`54ece48ab`, `20262718e`), whose
write shows a remark of one source false as stated in finite rational rank,
and four independent answers to one request on definable class
well-orders beyond `Ord` were merged as Part XVI of `surreal-well-orders`
(`111c38012`, `62b16914e`). Reciprocal notes (`90b2d40e6`) went to
`open-query-membership-games`, to five surreal reports
(`birthday-cutoffs-and-hereditary-sets`, `surcomplex-field-automorphisms`,
`omnific-preserving-automorphisms`, `hahn-evaluation-at-omega`,
`foundations`) and to the README of `Algebra/BakerCampbellHausdorff`. The
Hilbert's-tenth research tree reviewed the archives before placement
(`8dffc7af0`, `3abf23ba1`, `3d87c3d6b`, `18825ee16`, `1eab36bb3`,
`556836e9b`, `fcc4098ec`), authenticated the placements (`608e06daa`,
`b16786caf`, `ccb0bba7f`), confirmed the hat-seed correction independently
(`c52f7d055`) and reviewed the four writes within stated scopes
(`47ab39154`; `6d78c238d`, after `6d06f8952` corrected the guide's sentence
that no Part III review existed; `9280aa6d4`, which corrected three
editorial statements of the Polish report; `ec4b972db`, three metadata
claims of Part XVI). Nothing was superseded, and no manuscript refutes a
repository claim.

Batch 97, seven archives in two arrival commits (`d7cf7d554`,
`e88ed8bf6`), was placed in four clusters, two of them here. 97G added
Section 17 to
[`a279619-level-seven-gamma-constant`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279619-level-seven-gamma-constant)
(`a4542b8a3`, written in `3412ae074`), from a manuscript written with the
report in hand: global strict log-convexity, a Hankel matrix strictly
totally positive of order 5 but not totally nonnegative of order 6 (with
`D₆(1) < 0` and a 21-polynomial positivity certificate), the exact
twelfth-moment obstruction and a fixed-order Hankel expansion with
generator; this answers the report's research question R6. The write added
Subsection 17.10: a square-root singularity at `z = −1`, hence no Stieltjes
tail and a Hamburger measure, if any, confined to `[−1, 27]`; the
independent check `57ccadf2d` found no gap and added one sentence, and
`f70ab0c7d` fixed two links, the description of an Apéry report's Part III
and a note date. Its OEIS draft is staged as data and was never submitted.
97H added Parts IV and V to
[`a189281-path-forest-expansions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions)
(`5a69916e8`, written in `eea159818`), two manuscripts sharing no theorem:
an all-orders expansion uniform over every pair of path forests in subpath
densities, with the short-path term (Part IV), and a Borel completion of
A189281 with a Dawson kernel, sharp Borel growth, no summability in any
open sector and a flat remainder nonzero at least once in every four
indices (Part V). The write refuted, retaining them, two small claims of
the Part V manuscript (a table entry and its count of sign changes,
Remark 66.1); the Hilbert's-tenth publication review `8bba916ca` repaired
one notation slip. The other four archives went elsewhere: a fifth answer
to batch 96's request on class well-orders beyond `Ord`, arriving fifteen
minutes after that placement, became Part XVII of the surreal report
`surreal-well-orders` (`6571ee1af`, `a21a42d8c`, merged with a concurrent
review in `5908f9de7`), whose write also repaired four statements of Part
XVI after an independent check; and three continuations of the Fabius
programme (Hölder–Zygmund spectra, zero-bias occupancy, finite-factor
Wasserstein contact) were filed whole in the Fabius drafts tree
(`41f53f7d8`), their editorial pass deferred. Reciprocal notes
(`c04452509`) went to `apery-hankel-determinant-growth`,
`stirling-hankel-obstruction`, `a239144-forbidden-distance-involutions` and
the surreal `foundations` report. The Hilbert's-tenth research tree triaged
the six analytic archives (`37af2f0d6`) and reviewed the class-order
archive (`39bb02ece`), its placement (`cd4799536`) and the Part XVII
publication (`65969409c`, which corrected three guide claims and
empty-domain cases of Part XVI, each retained with a counterexample).
Nothing was superseded, and no manuscript refutes a repository claim.

Batch 98, twelve archives in two arrival commits (`2172df76a`, eleven;
`1ec443bc4`, a late twelfth), opened no report: every manuscript continues a
collection report and became a new Part of it, placed in four commits. 98A
(`9353a7171`) added Part III to
[`a000571-tournament-score-sequences`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000571-tournament-score-sequences)
(written in `a763feee1`: the supercritical side on a fixed small interval of
weights, pole–branch expansions to every fixed order through coalescence,
tempered 3/2-stable and Gaussian block counts and a Gumbel maximum; the
stable count law at the critical weight itself is credited to
Banderier–Flajolet–Schaeffer–Soria), Part II to
[`valley-monotone-bargraphs`](enumerative-combinatorics/valley-monotone-bargraphs)
(`abdad4eef`: the exact critical valley weight, a `1/n` critical window, and
the lattice-Gumbel law of the maximum height, answering the extreme-height
half of Part I's question 10.4) and Part II to
[`a122399-surjection-diagonal`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a122399-surjection-diagonal)
(`77fff37e3`: the block defect as a sum of independent Bernoulli variables,
`Poisson(e^{−c}/2)` at `n = m(log m + c)`, Edgeworth expansions and an
all-orders inverse with the certificate `N_{1/e}(1000) = 6207`). 98B
(`0fba5167f`) added Part II to
[`a181199-shifted-rectangles`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles)
(`b71545625`: every fixed height a rational diagonal, hence D-finite, and the
rare boundary count `R_m(n)`; the write corrected the manuscript's framing
that Part I's Questions 4 and 7 were settled, since `R_m` is a much smaller
sector of the boundary error and D-finiteness says nothing of the minimal
order; Parts III–V followed in batch 101), Part II to
[`a033552-catalan-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a033552-catalan-partitions)
(`b21eab238`: two independent manuscripts answering Part I's questions 10.4
and 10.5, merged with base 06, shared theorems printed once; the write
proved 06's unproved covariance candidate), Part II to
[`a273821-first-pattern-failure`](enumerative-combinatorics/a273821-first-pattern-failure)
(`246175583`: the patterns `1(r+1)r…2`, answering Part I's first question),
Part III to
[`a261781-matrix-compositions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions)
(`324818ddb`: the Cauchy limit of the Hankel zeros with the sharp
Kolmogorov constant `9/π²`, answering Part I's Research question 7) and
Part II to
[`a238016-restricted-partitions-cubic-boundary`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a238016-restricted-partitions-cubic-boundary)
(`a4198a037`: one expansion uniform for `N ≥ a m²`, the centred threshold
`m^{5/2}` and transition scales `m^{2+1/(2r)}`, answering Part I's question 2
and the `α → ∞` end of Section 14.6 of `a097356-sqrt-restricted-partitions`).
98C (`b50febf79`) merged two independent answers to Part I's Question 1 of
[`a182220-source-boundary`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a182220-source-boundary),
natural boundaries of every fixed-defect series, as Part II with base 05
(`ed438414b`). 98D (`3b9458b31`) placed the late arrival, a general
lattice-peak transfer theorem, as Part II of
[`a357825-theta-ballot-power-sums`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a357825-theta-ballot-power-sums)
(`2b257ba94`), answering its question Q6 in a sufficient-hypothesis form; the
write proved the critical window of `a380274-mahonian-growing-powers` an
instance. None of the twelve went to `Analysis/Transseries`: their
expansions are fixed-order power–logarithmic ones (the `5a69916e8`
precedent).

Under the standing rule, the 98D manuscript's identity for `Σ u³e^{−qu²/2}`
is false as printed (it drops `2q^{−2}∂_δϑ`) and is corrected on record, and
its claim that Part I's all-orders coefficients are "precisely" its own holds
at first order only; the shifted-rectangle manuscript's two overstatements
are corrected as above, and a122399's "transseries" is recorded as a
depth-one power–log expansion. Repository statements made stale ("Q6 stays
open" in `a357825` and in `a380274-mahonian-growing-powers`; "no
natural-boundary claim" in `a182220`; Section 14.6 of
`a097356-sqrt-restricted-partitions`; the open questions answered in each
host) carry dated notes. Reciprocal notes for batch 98 went to
`a261781-matrix-compositions` (a122399's Poisson defect),
`a097356-sqrt-restricted-partitions` (Section 14.6 re-scoped to `α → 0`),
`a003407-dyadic-scaling-rigidity` (a182220's transfer lemma, a method only),
the READMEs of `a181280-binary-matrix-formula` and
`a047874-long-increasing-subsequences`, and `a380274-mahonian-growing-powers`
(the batch-98 half of `639b038ab`). The intake's independent checks found
every result the writes added valid and corrected: the range on which a
proof gives uniqueness in `valley-monotone-bargraphs` (`1ee6d763b`), an
impossible regime named in `a122399`'s necessity note (`1fffcbef0`), one
decimal and the order of a step of the inverse in `a238016` (`cf204d897`),
two values of a numerical note in `a182220`, where the check also derived
when the radial ratio of an arithmetic section has a limit (Corollary 21.7,
`978b52fb5`), and two wordings in `a357825` (`2ff7e46eb`); the checks of
`a033552` (`f00cfc175`) and `a181199` (`ed8e73df9`) needed no correction.
The new Parts of `a000571`, `a273821` and `a261781` have not been
independently checked. Staged files are byte-identical to the deliveries
(fifty-three CRLF files kept by `-text` lines); the articles, PDFs, delivery
READMEs, checksum manifests and a few byte copies survive in the arrival
commits. Nothing was superseded, and no manuscript refutes a repository
claim.

Batches 99 to 113 are the clusters of one delivery: the session bundle of
numbered Research Reports 1–243, 177 archives in one arrival commit
(`60f54ea06`), triaged into fifteen batches (99 to 113). Batch 99 went to
the Fabius drafts tree; batches 100 to 108 are placed and catalogued below
(108 with its writes pending); batches 109 to 113 are not yet placed. Batch
114 is the other arrivals of the same day.

Batch 99 brought nothing here: its thirteen archives, taken from the
session bundle `60f54ea06` (Thue–Morse trace and interval parts, a checker
repair and the first-return package, Report 80), were filed whole in the
`thue-morse/` group of the Fabius drafts tree (`9985d6ed6`).

Batch 100, eleven archives of the session bundle's arrival commit
(`60f54ea06`, Reports 1–243), was placed in one commit (`36571ae0e`) in
seven clusters and opened four reports in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics):
[`a126348-stable-hilbert-series`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a126348-stable-hilbert-series)
(Report 84, written in `231237c5c`: all-orders coefficient asymptotics of
`∏(1 + qᵏ/(1 − q))` with explicit `C_1`, `C_2`, a minor-arc bound without
resonance sectors and an explicit range inverse; its exact modular
factorization is identity (11) of `a291698-moving-fugacity-partitions` at
`u = 1/(1 − q)`, credited at the write),
[`a307316-leafless-multigraphs`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a307316-leafless-multigraphs)
(Report 131, `26088828f`: `H_m ≲ C_m ≤ A_m ≲ e^w H_m` with `w = W(2m)`,
`C_m/A_m = 1 − O(w³/m)` and an `O(1)` threshold inverse; the upper half rests
on Wright's 1972 theorem, which the source saw only in an OCR'd copy and an
abstract),
[`a007716-bipartite-multigraphs`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a007716-bipartite-multigraphs)
(Reports 88 and 92, `72091374c`: `a_n ~ B_n² e^{W(n)²/2}/n!` with every fixed
order, and the rare-symmetry law `2W(n)³/n` and connectivity expansions for
A007718) and
[`a271619-strict-twice-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a271619-strict-twice-partitions)
(Reports 182 and 181, `aa4a1136f`: a two-charge phase-resolved expansion for
A271619, an eventual result whose leading formula is still about 562 times
too small at `n = 5000`, and every fixed order, inversion and Gaussian and
Gumbel laws for A358836). It added Part IV to
[`power-tower-exponent-supports`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-exponent-supports)
(Report 59, `1b247299e`: Hermite limits with a first correction on fixed
defects of `x^(√x)` and `O_r(√X)` cancellations per defect), Part VI to
[`matching-rank-normalization`](log-concavity-and-unimodality/matching-rank-normalization)
(Report 81, `f4dabd895`: the third Newton inequality `9p_3² ≥ 16p_2p_4` at
matching number six with one weighted shore, leaving only the fourth gap
open) and Sections 21–22 to
[`a022629-distinct-partition-norms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a022629-distinct-partition-norms)
(Reports 89, 82 and 93, `2ef752171`: the smooth lattice-minus-integral sector,
`P_9`, `P_10`, `Δ_9`, `Δ_10` and an exact-range inverse; and a critical theta
window for powers growing like `(2n)^{1/6}/log n`). Merges: Report 92 is a
sequel to Report 88 (base) and answers its rare-symmetry question at leading
order; Reports 182 (base) and 181 share no theorem; in Section 21 Report 89
(every real `α`) is the base and Report 82 its case `α = 1`. About half of
Report 59, and the core theorems of Reports 82 and 89, re-prove results
already in their hosts and are printed as second routes or tabulated; Report 59's
contribution sentence is kept with a dated correction. Report 93 is the
Fourier-dual form of the lattice-peak transfer theorem of
`a357825-theta-ballot-power-sums` Part II, not a corollary of it. Two
repository statements became stale and carry dated updates ("gaps three and
four are open" in `matching-rank-normalization`, "no theorem for growing α"
in `a022629-distinct-partition-norms`). Excluded from staging and
retrievable from `60f54ea06`: PDFs, checksum manifests, byte copies of
repository files, Report 81's prerequisite archive (source 05 of its host)
and three of its files over 1 MB, and Report 182's 1.43 MB coefficient
table. Reciprocal notes went to `a260700-parabolic-double-cosets`,
`preorder-root-polytopes`, `power-tower-derivative-term-counts`,
`a291698-moving-fugacity-partitions`, `a022629-distinct-partition-norms` and
`a357825-theta-ballot-power-sums` (the batch-100 half of `639b038ab`). The
intake's independent checks found every result the writes added valid and
corrected three statements: a truncation error quoted in `a126348`
(`f8accf37c`, which also confirmed the merge's two-right-vertex remark in
`matching-rank-normalization` and Proposition 9.1 of `a307316`), the
outlook of Part IV of `power-tower-exponent-supports`, now restricted to
`1/2 ≤ a < 1` (`0c81c51e2`), and the order of the theta shift of the
threshold in `a022629` (`91ef1ef6f`); the check of `a271619` (`342a4583e`)
found both of the write's proofs valid. Nothing was superseded, and no
manuscript refutes a repository claim.

Batch 101, thirteen archives of the 177-archive session bundle that arrived
in `60f54ea06`, all OEIS-asymptotics manuscripts, was placed in one commit
(`f7c612c72`) as six additions and one new report; the placement overturned
one triage call (Report 232 is an addition, not a new report). Report 96
became the new report
[`a196275-column-convex-permutominoes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196275-column-convex-permutominoes)
(written in `5a1d923db`): a Bernstein-basis operator turns Tomás's
recurrence into the closed form of the factorial-normalized generating
function, an exact spectral measure and `a_n ~ k (n+1)! h^n` with
`h = 1/(1 − W_0(1/e))`, with all-orders secondary sectors, rounding of the
envelope inverse for every `n ≥ 1` and non-P-recursiveness; its two
byte-identical 1.26 MB exact-count tables were excluded as regenerable, and
its literature-status claims are unchecked. Reports 231 and 233 became
Parts III–IV, and Reports 85 and 91 Part V, of
[`a181199-shifted-rectangles`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles)
(`ca1668212`): proofs of the A181198 and A181199 recurrences that OEIS
displays as conjectural and of Kauers–Koutschan's Conjectures 18–19, and two
earlier independent routes (dated 1–2 October, before Parts I–II) to Part
I's expansion, the algebraicity dichotomy and Part II's rational-diagonal
theorem, a chronology the report credits. Reports 90 (base) and 86 became
Part VI of
[`a215561-fixed-composition-excursions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a215561-fixed-composition-excursions)
(`013b32fca`): fifth and sixth proofs of its main theorems, the second
A215570 correction without the recurrence and strict monotonicity of every
row; Report 86's "lattice factor 4" is shown not to be an instance of the
lattice-peak transfer theorem of `a357825-theta-ballot-power-sums`. Reports
87 and 94 became Parts III–IV of
[`a113226-vincular-avoiders`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113226-vincular-avoiders)
(`07fd071f8`: a second exact route with non-D-finiteness, and exact Hankel
sectors answering Part I's Question 4 for each fixed sector); Report 95
Part III of
[`a126764-lconvex-polyominoes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a126764-lconvex-polyominoes)
(`e8055d890`: a third, fully written proof of the all-orders coefficient
theorem); Report 98 Part III of
[`a330266-balanced-smirnov-poisson`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson)
(`a75a4e41b`: a second repair of the tail step, from the same pin as Part
II, with the `n^-4` terms); and Reports 83 and 232 Parts VI–VII of
[`a189281-path-forest-expansions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions)
(`e9994117b`: a same-day third derivation printed by its additions only,
and the joint expansion for two reciprocal gaps, with the camel and knight
coefficients 48 and 28). Re-proofs of host results are printed as marked
second routes or tabulated, and unproved claims went to each Part's
further questions. The a189281 write also applied the reciprocal notes that
correct its two stale sentences about a330266's tail step; the notes into
`a181280-binary-matrix-formula` (the Section 6.4 recurrences now proved) and
`a357825-theta-ballot-power-sums` (Report 86 examined, not an instance) are
not yet applied. The intake checked every write independently: `39b1110a6`
sharpened the a196275 profile bound to an exact distance, `07068a4b9`
tightened one proposition on unequal ranks in a330266, `af05d23ba` sharpened
an edge constant of a126764's Lemma 28.1 by the factor `1/π` its proof
gives, `a368aed3c` corrected
a false sentence of a113226's write on the decay of the reversion terms,
`aab6be85d` refined three wordings in a215561, `9830327b9` narrowed a189281's
claim that an enclosure checks `c_12`, and `6e4dbcd38` found and proved
lower-degree recurrences of higher order for A181198 and A181199. The
Hilbert's-tenth research tree's bounded review (`e5e401a81`) found no
Turing-complete simulation or paid Diophantine compiler and no defect.
Nothing was superseded, and no manuscript refutes a repository claim;
statements of several hosts that the new Parts made stale carry dated notes.

Batch 102, thirteen archives of the session-bundle arrival `60f54ea06`
(bundle Reports 97, 99–105, 107, 108 and 241–243), all on ascent sequences
or on Airy amplitudes of trees, networks and automata, was placed in one
commit (`6ab1f1979`) in six clusters, all in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics).
It opened three reports:
[`a098569-self-modified-ascents`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a098569-self-modified-ascents)
(Report 242: self-modified ascent sequences as positive-diagonal tables,
A098569 and A121690, with an expansion to every fixed order at the exact
gamma saddle, a local Gaussian law for the dimension that answers the
question of A098568 on its row distribution, the binary probability
`e^{−u²/2−u}(1 + 𝓡(u)/N + …)` and two-ceiling inverse brackets; written in
`3daaab24e`),
[`a202059-ascent-100-110-growth`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202059-ascent-100-110-growth)
(Reports 243, the base, and 241: the linear logarithmic constant
`log 2 − 1` for A202059, a bracket for A202060, and, from the earlier
Report 241, which keeps priority, the refutation of the
`Γ(3n/4+1) μⁿ n^g` scale conjectured by Conway, Conway, Elvey Price and
Guttmann and the non-P-recursiveness of the three classes; written in
`3ed50db4e`) and
[`a336070-weak-ascents`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a336070-weak-ascents)
(Reports 105, the base, 107 and 108 in chain order: factorial root `6/π²`
for every fixed difference parameter `d`, the correction `(d/2)(log n)²`
with `O(log n)` remainder, level weights with a full large-deviation
principle, and bounded-error inverses; Report 108's Sections 3–4 repeat
Report 107's and are printed once; Report 105's uncredited binomial
transform is credited to Jelínek at the write; written in `32122c09e`). It
added Part V to
[`a202058-ascent-000-growth`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202058-ascent-000-growth)
(Report 97: a two-catalytic functional equation, the endpoint constants
`1 − 8/(3π)`, `1 − 4/(3π)`, `4/(3π) + 8/(3π²)` and third and second
routes to the root and ratio limits) and Part III to
[`a294220-ascent-multiplicity-caps`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a294220-ascent-multiplicity-caps)
(Report 99, which strictly generalizes Report 97 by the same method: the
ratio limit for every fixed cap, answering the host's Question 2,
endpoint laws and a large-deviation principle), both written in
`b71fda5be` and kept in separate hosts as batch 77 split them (cap two in
one report, the other caps in the other); Part V to
[`a082161-airy-amplitudes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a082161-airy-amplitudes)
(Reports 100, 101, 103: second routes in even time and Report 100's proof
that the relaxed amplitude is positive without the published lower bound
every earlier Part uses; `3e71ff1e6`); and Parts III–IV to
[`a213863-tree-child-networks`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a213863-tree-child-networks)
(Reports 104, the base, and 102, both closed before the host's sources
arrived and credited as independent routes: closed forms of the first two
coefficients for every degree, a conditional first total-count correction
at `d = 3`, and the fifth and sixth binary coefficients; `7e85b5a0c`). The
cross-references among the seven reports were written into the writes
themselves; no separate reciprocal-notes commit was made, and the drafted
one-line pointers from `a202061-ascent-120-deficit` and
`a202062-ascent-201-enumeration` to the new 100/110 report are not
applied. Independent checks after the writes found no counterexample and
no gap in any proof chain, and corrected wording only: `811ad87f0` located
the sign change of the first saddle correction in the A098569 report
(`N = 15,865`, not "between 10⁴ and 10⁶") and, with `5ada42e2f`, withdrew
the claim made in both new ascent reports that Report 242's elementary
carrier implies Report 243's whole triangular lemma (it gives the sum
estimate, not the single-term one); `71f343e25` restricted a doubling
inequality to `i ≥ 1` and fixed the coefficient for real `d` at `⌈d⌉/2`;
`edb875773`, `84cd75b5a` and `c5fcc3348` adopted clarifications, the last
stating the two dependencies of the write's Corollary 66.3 in the Airy
report. A relevance review in the Hilbert's-tenth research tree
(`c6dea60c7`) found no Turing-complete interface in the batch. Reports
100, 101 and 102 carry the line "Research prepared for private review",
disclosed in their reports; manuscripts of the additions, PDFs, checksum
manifests, byte copies and 154 empty run records were not staged and
remain in `60f54ea06`. Nothing was superseded. Report 241 refutes a
published conjecture, and Reports 97 and 100 make statements the
repository had already overtaken (dated notes); no manuscript refutes a
repository claim.

Batch 103, eleven archives of the session bundle's arrival commit
(`60f54ea06`, bundle Reports 106, 109–117 and 130), was placed in one
commit (`9c995cefe`) in seven clusters, all in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics).
It opened four reports:
[`a348351-one-sided-rectangulations`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a348351-one-sided-rectangulations)
(Report 111, written in `0c2cdf435`: `log a(n) = n log Γ − α log n + o(log n)`,
`Γ = (7+√17)/2`, the exponent half of the Asinowski–Cardinal–Felsner–Fusy
conjecture, with the amplitude open; the generating function is not
D-finite; a two-term threshold inverse),
[`a008608-tesler-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a008608-tesler-matrices)
(Report 106, `17d995b94`: the second term `−(3/4) n log n` of `log a_n` for
regular Tesler matrices, whose leading term `π√(8/27) n^(3/2)` is
Balashov–Bulavenko–Molybog's; O'Neill 2018, uncited by the manuscript, added
at the write),
[`a345470-self-complementary-scores`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a345470-self-complementary-scores)
(Reports 116 and 114, `1b792e07a`: `C_n ~ A 2ⁿ n^(−3/4)` for A345470 and the
strong fraction `D_n/C_n → e^(−λ)` with `a000571-tournament-score-sequences`'
`λ`, Lambert-`W₋₁` inverses, and the first proof of the `Θ(2ⁿ n^(−3/4))`
growth with monotonicity) and
[`a135501-closed-lambda-terms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a135501-closed-lambda-terms)
(Reports 110 and 109, `b432720bf`: every fixed inverse-logarithmic order of
`log A_s(n)` for A135501 and A220894 with a controlled inverse, and a joint
large-deviation law for the abstractions and unary height of a random closed
term). It added Part III to
[`a377922-corner-polyhedra-schnyder`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a377922-corner-polyhedra-schnyder)
(Report 112, `9b4001d29`: a log-scale cone theorem for walks with a finite
internal state and unbounded steps, which the host had disclaimed, the
six-face sleeve injection and non-D-finiteness from the log-scale law),
Parts II–IV to
[`a333497-historic-trees`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a333497-historic-trees)
(Reports 113, 115 and 117, `6603ab5a8`: second routes to the orders five,
seven and 59, and the new theorem that A333497 and A336009 are not
P-recursive) and Part II to
[`a116379-bounded-identity-trees`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a116379-bounded-identity-trees)
(Report 130, `a2dc5d320`: rational-interval certificates of the constants for
`d = 3, 4`, under which every 30-place value of Part I is correctly rounded).
Merges: Report 110 is the base of the lambda report and settles Report 109's
open `n/log n` coefficient and, through a write remark, its ratio frontier
to leading order, so Report
109's growth theorem and inverse are printed as superseded second routes;
Report 116 is the base of the self-complementary report, and Report 114,
written first, keeps its growth theorem as a second route and its
monotonicity as new. Report 112 never saw Parts I–II of its host, and
Reports 113, 115 and 117 never saw Part I of theirs; their re-proofs are
printed as marked second routes, their novelty sentences with dated notes.
Report 111 is the earlier, model-specific proof of Report 112's cone theorem
(its walk satisfies the hypotheses, Remark 1.2 of the a348351 write); the
two reports stay separate and cross-referenced. The placement overturned one
triage call: the self-complementary scores became a new report, not Parts of
`a000571-tournament-score-sequences`, which shares no theorem or question
with it. One external published statement is wrong: both
self-complementary manuscripts copy the limit density of Denisov–Wachtel's
Theorem 1 (AIHP 2015), which has mass `0.1154552960…`, not 1; the write
proves that the Groeneboom–Jongbloed–Wellner density cited by the same paper
has mass 1, re-derives the amplitude formula, and repairs the one lemma that
used the printed shape. Excluded from staging and retrievable from
`60f54ea06`: the manuscripts of the additions and merged members, PDFs,
checksum manifests, byte copies and Report 130's two regenerable coefficient
exports; nine delivered `.log` records were force-added. Reciprocal notes:
a348351's into a377922 were applied in the a377922 write (`9b4001d29`) and
updated by the a348351 check; the drafted pointer from
`a000571-tournament-score-sequences` to the self-complementary report, whose
"no other report treats tournament score sequences" sentences are now
incomplete, is not yet applied. The intake's independent checks found every
result the writes added valid and corrected supporting text: a range and the
algebraicity step in a348351 (`019cf8e50`); O'Neill's journal and arXiv
numbering, Pantone's credit and the completion of the margin-sharpness proof
in a008608 (`42c8a99c8`); a scale label and a coefficient in a377922
(`f8bcc8515`); the extent to which Part IV replaces Part I's
strong-k-positivity step and the Mallet-Paret–Smith credit in a333497
(`0c4719e03`); three sentences in a135501, adding the check's tilt as
Proposition 18.2 (`24e36bc20`), whose large-`N` range a second check fixed
(`f1c0e8d8c`); the predicted amplitude `0.0374` and the Monte Carlo
evidence in a345470, replaced by a dynamic programme of the conditioned walk
to `n = 600` (floating point, extrapolated) that confirms the corrected
density (`78a7cef4a`); and in a116379 a criticism the write had made of a
manuscript proof, withdrawn, and one digit (`1cb706454`). The Hilbert's-tenth
research tree reviewed the two lambda archives as computational-substrate
candidates (`c0cb99917`) and the lambda publication and its revisions
(`ca8221993`, `f5b09f57d`, `479871ca4`), and proved in `a8455335c` that the
ratio limit `1/2` holds for every diverging `α = b/u`, beyond Proposition
18.2 (not incorporated in the report). No archive was superseded, and no
manuscript refutes a repository claim.

Batch 104, twelve archives of the session bundle's arrival commit
(`60f54ea06`, bundle Reports 118–129), was placed in one commit
(`612787fb4`) in two triage clusters, all in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics),
and opened four reports. The triage's eight-source cluster on the
inversion-sequence classes of Britt and Beaton (arXiv:2512.21943v3) was split
by method into three reports, since the manuscripts share no lemma and cite
each other nowhere (the A202058/A202061/A202062 precedent):
[`a279544-inversion-kernel-classes`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279544-inversion-kernel-classes)
(Reports 118, base, 119 and 122, written in `37c5ebe97`: kernel-orbit proofs,
to every fixed order and with certified amplitudes, of Britt and Beaton's
non-rigorous laws `a_n ~ C μⁿ n^(−3/2)` for A279544, A279567, A279569 (and
the Wilf-equivalent class 1953B) and A279558; Kotěšovec's OEIS amplitudes lie
in every certified interval, so no digits are new),
[`a279571-inversion-cone-walk`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279571-inversion-cone-walk)
(Reports 125, base, and 123, `4d3a6730f`: `a_n ~ C_A 9ⁿ n^(−κ)` with
`κ = 1 + π/arccos(2/√7)`, a threshold inverse and non-D-finiteness; the
write shows that Report 123's walk satisfies (H1)–(H4) but not (H5) of the
log-scale cone theorem of `a377922-corner-polyhedra-schnyder` Part III, so
its exponent follows from that theorem's proof, not its statement) and
[`a279551-inversion-log-deficit`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279551-inversion-log-deficit)
(Reports 126, 127 and 129, base, printed in dependency order 126, 127, 129,
`80adcb910`: the deficit `σ_D n^(1/3)(log n)^(2/3)` of A279551 and A279556
with its `log log n/log n` term and non-D-finiteness, by the method of
`a202061-ascent-120-deficit`; a write remark proves that no stretched
exponential form is an equivalent, which refutes Britt and Beaton's
numerical `n^(3/8)` forms). Reports 128, base, 124, 121 and 120 became
[`a005163-diagonally-symmetric-asms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a005163-diagonally-symmetric-asms)
(`ed4d0a12f`): the full leading equivalent
`a_n ~ C_* e^(αn² + βn) n^(−5/72)` of diagonally symmetric alternating sign
matrices, the leading term of Behrend–Fischer–Koutschan's Conjecture 11.1,
with fugacity pressure and limit laws; Report 124 is printed in full because
the base depends on it, and the sections Reports 120, 121 and 124 share are
printed once. Not staged and retrievable from `60f54ea06`: PDFs, member
manuscripts and delivered READMEs, checksum manifests, embedded copies and
byte copies of repository files. Reciprocal notes (`32919c4cf`) went to
`a377922-corner-polyhedra-schnyder`, whose Section 22.5 and README had
called Report 123 unplaced, to `a348351-one-sided-rectangulations`, whose
Question 1 named Report 125 as "to be filed by a later intake batch", and to
`a202061-ascent-120-deficit` (a "same method, other sequences" note). The
intake's independent checks found every mathematical claim valid and
corrected: in a279544 the write's statement that every Part proves a
Lambert-`W₋₁` inverse (Part III's expands in powers of `1/log M`), with a
precise Martinez–Savage citation (`cc8144111`); in a279551 two twice-rounded
residual-table entries, extending the write's exclusion to a factor
`(log n)^γ` (`b54142448`); in a005163 "interlacing" to weak interlacing in
two notes and three statements of uncertified evidence, among them the
amplitude estimate `0.7235287`, first printed `0.7235288` (`77cec68db`); in
a279571 nothing (`1c7e526c7`). The Hilbert's-tenth research tree reviewed the
A279551 publication (`76e197985`: the bare length support of both classes is
every `n`, a deduction for that programme, not an error of the report) and
triaged A279551 and A005163, with batch 105, for computational relevance
(`97b95bd35`: none in the inspected scope). No archive was superseded, and no
manuscript refutes a repository claim; the only refuted statements are
Britt and Beaton's own non-rigorous numerical forms.

Batch 105, thirteen archives of the same arrival commit (`60f54ea06`, bundle
Reports 134–146), was placed in one commit (`e85586b7c`), all in
[`oeis-sequence-asymptotics`](generating-functions-and-asymptotics/oeis-sequence-asymptotics),
and opened four reports.
[`a217057-unique-pattern-occurrences`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a217057-unique-pattern-occurrences)
(Reports 134, 135, 137, base, 136, 138 and 140, written in `84c52f028`)
proves leading amplitudes, rational-diagonal D-finiteness and expansions to
every fixed order for the permutations with exactly one 1234, 1243 or 12345
(A217057, A224179, A224248): logarithms from the third order for 1234, none
for 12345. Report 134 refutes Conway and Guttmann's conjecture `R = 1/2`
(EJC 32(1) P1.3) with a rational certificate `R > 0.50009`, which the write
sharpens to `R > 0.50153`; their `149/160` for one 1243 stays open. Report
139 became the separate report
[`a224182-unique-1432-order`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a224182-unique-1432-order)
(`bb5ca9433`), its method sharing nothing with the others: `b_n = Θ(9ⁿ/n³)`
for one 1432 with explicit constants `1/2187` and `81`, without a computer,
and a computer-certified exact image (2,074 cores). The write found that the
one-step bound in Mansour, Rastegar and Roitershtein's proof, which the
source and the placement had taken to give the upper order, is justified by
its argument only with a factor `n²`, and that the ratio `b_n/(nA_n)`, which
the placement called rising, first falls at `n = 18`. Reports 141, 142, base,
and 143 became
[`a292692-weighted-dyck-newton-diagonal`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a292692-weighted-dyck-newton-diagonal)
(`42721c521`): Bala's Riccati and continued-fraction conjecture on A258219,
Kotěšovec's asymptotic form and growth-rate conjecture for A292692 with the
amplitude in closed form, every fixed order on the interior and the
upper-edge transition. Reports 144, 145 and 146, base, became
[`a398540-proportional-placement-game`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a398540-proportional-placement-game)
(`0480c6184`): a computable rate, `W_n ~ r_* √(2πn) r_*ⁿ`, which corrects
the prefactor `√(2π)` of Serra's manuscript, the logarithmic corrections and
every fixed order; the write proves, as well, that Serra's integral equation
(read through the profile), his pure-power ratio expansion beyond the first
order and his log-convexity reading fail. Report 146 was corrected in place
before delivery and its earlier version was never received. In every merged
report the Parts are printed in dependency order, and embedded byte-identical
copies of earlier Reports once. Not staged and retrievable from
`60f54ea06`: PDFs, member manuscripts and delivered READMEs, checksum
manifests, embedded copies and duplicates; Nakamura and Zeilberger's
enumeration output `oF12345a` (counts, no stated licence) is staged with
attribution. Reciprocal notes (`c8fd19e36`) cross-reference the two pattern
reports and point `a047874-long-increasing-subsequences` to the first. The
intake's independent checks found no mathematical error in the manuscripts
and corrected the writes: in a217057, after rerunning the refutation by an
independent count, two wordings (`a4f4d8ceb`); in a224182 three wordings
(`c437f27be`); in a292692 a false positivity note of the write and the
transseries citations (`159c9a901`); in a398540 the write's attribution of
its profile to Serra (his Step-2 ansatz carries his amplitude, and the limit
is `1 − C²/(2πr_*)`), a missing step of Remark 33.3 and the transseries
citations (`c5f63aa29`). The Hilbert's-tenth research tree triaged A398540
and A224182 for computational relevance (`97b95bd35`) and found none in the
inspected scope. No archive was superseded, and no manuscript refutes a
repository claim; the refutations are of external statements (Conway and
Guttmann's `R = 1/2`; Serra's prefactor, integral equation, expansion and
log-convexity reading).

Batch 106, twelve archives of the session bundle's arrival commit
(`60f54ea06`), was placed in one commit (`47fc7a069`) as seven new reports
in `generating-functions-and-asymptotics/oeis-sequence-asymptotics/`, one
per subject, and each was written on its own. Bundle Reports 149 and 151
(`742754a50`) became
[`a347546-alternating-baxter-involutions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a347546-alternating-baxter-involutions),
with the fixed-point refinement as Part II. Part I shows the even formula of
Min's 2021 recurrence false (the outer blocks of an even involution are
mutual inverses, so the outer factor is Catalan): the class has 2168 members
of length 20, not 2166. The write proves that the recurrence falls strictly
below the class at length 20 and every length from 22 on, so Min's printed
list at 20 and 22–26 and 21 of the 42 OEIS terms of A347546 are wrong
(definition right), and credits Guibert and Linusson for the Catalan count
that Part I re-derives. Reports 150 and 152 (`c6557f9c9`) became
[`a156808-circle-graphs`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a156808-circle-graphs)
(the leading equivalent `e^{−3/2}(2n−1)!!/(4n)`, then the first corrections;
the second coefficients depend on an unknown prime constant), Report 153
(`6fb3059e5`)
[`a123448-permutation-graphs`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a123448-permutation-graphs)
(`a_n = (1/4) Σ h_k (n−k)!` to every fixed order), and Report 133
(`c6488293e`)
[`a005975-interval-graphs`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a005975-interval-graphs)
(half the Fishburn numbers with a `−F_{n−2} log n` correction); the three
graph reports share a pipeline but no statement or citation, so they were
kept apart. The write of Report 153 corrected two statements of the
placement record. Report 153 carries no "prepared for private review" line:
the phrase occurs in no delivered file, and the only hits are packaging
negations such as "nor private review documents". Nor is Report 153 the
first answer to Johnston's 2020 question whether the count is `o(n!)`:
Bassino, Bouvel, Féray, Gerin and Pierrot (arXiv:2402.06394v1, 2024) had
already shown `a_n ≥ n!/30` for large `n`, so the answer is no; what Report
153 adds is the constant `1/4` and every fixed order. The write of Report 133 read Hanlon (1982),
who lists the asymptotic count of interval graphs as open, which settles the
placement record's caveat that its leading term might be classical. Reports
147 and 148 (`8f7baed2b`) became
[`a252782-diagonal-euler-transforms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a252782-diagonal-euler-transforms):
the `n²`-th root tends to `3^{1/3}`, which refutes the `e^{1/e}` conjecture
stated in A252782 and A270917; the write's bound
`A(n) ≤ 2^{n−1} 3^{n²/3}` puts the root below `e^{1/e}` for every
`n ≥ 414` (the placement record's 415 is valid but not least). Reports 225,
226 and 228 (`84fc1aaed`), in dependency order, became
[`a290354-iterated-euler-diagonals`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a290354-iterated-euler-diagonals),
proving the form of Kotěšovec's conjectured asymptotic for A290354 (the
digits of its constant uncertified). It is a separate report and not a
Part of `a139383-iterated-bell-diagonals`; the two share Report 228's
conjectured amplitude identity as a further question. Report 223
(`44ebdfef9`) became
[`a005121-strict-partition-chains`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a005121-strict-partition-chains),
Lengyel's numbers to every fixed order, recording a sign error in the
e.g.f. line of OEIS A005121 (nothing sent to the OEIS). Reciprocal notes
are in `3f9fc9d4f`: two dated notes and a README paragraph in
`a139383-iterated-bell-diagonals` (to `a290354` and `a005121`), and a
"see also" bullet in `a336070-weak-ascents` (to `a005975`). An independent
adversarial check of each write found no mathematical error, and each was
recorded with dated notes that keep the first wording: `3065f0ccf`
reclassified a252782's Theorem 7.2 as an instance of the transseries
volume's core reversion; `686e1e3ba` corrected a156808's factorial-core
side condition, which holds for every `L > 0`; `63482555d` confirmed
a347546's six corrected values of Min's list as direct counts; `cfc13c377`
sharpened a005121's OEIS remark and explained its depth-sum gap by the
`(log n)²/n` term of a139383's first correction; `b62ef2422` corrected
a123448's note on the 1990 table (the printed `a_20` rules out only IEEE
binary64) and confirmed `a_10` by enumeration; `20fdce33d` corrected the
quoted range of a005975's extrapolated limits; `a3a2d5582` withdrew a290354's
claim that Part II's restated interface was new. Embedded copies (Report
151's of 149, 148's of 147, 226's and 228's of 225 and 226) are
byte-identical and were not staged; nothing was superseded. Three external
errors are on record with proofs (Min 2021 Theorem 2.7, the OEIS `e^{1/e}`
conjecture, the A005121 sign), and no manuscript refutes a repository claim.

Batch 107, eleven archives of the bundle arrival `60f54ea06` (bundle
Reports 154–156, 158–160, 162, 163, 165, 205 and 207), was placed in one
commit (`3988bf5c4`) as five new reports under
`generating-functions-and-asymptotics/oeis-sequence-asymptotics/`. Reports
156 (base), 159, 158, 160 and 162 became
[`a238873-diagonal-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a238873-diagonal-partitions)
(`0ca2804be`): both journal conjectures of Archibald, Blecher, Elizalde and
Knopfmacher proved (`s(n)/p(n) → 1/2` for the subdiagonal partitions of
A238875, `q(n)/A(n) → 0` for the superdiagonal ones of A238873), the
subdiagonal ratio to every fixed order, the superdiagonal rate
`B = √(π²/3 + 4 log²2)`, Airy term and limit shape, and a full equivalent
`A(n) ~ K n^(−11/12) e^(B√n − D n^(1/6))` that is conditional on the
unrefereed preprint arXiv:2607.27504v1 and labelled so. The placement
message listed Gus Wiseman's OEIS conjecture in A238873 as addressed by no
manuscript and left it to the write; the write proved it (Proposition 1.3:
a partition has choosable initial intervals iff it is superdiagonal) and
credits the same argument, posted earlier by Clément Garrot in A387112
(comment of 31 August 2026), and the independent check added that it also
settles the conjectures of A388711 and A387112. Reports 154 (base) and 155,
two members of one Munarini family with different methods, became
[`a192563-factorial-stirling-products`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a192563-factorial-stirling-products)
(`774c233c4`), with an identity for the third member A192562 added by the
write. Reports 205 (base, its corrected revision 2; revision 1 was never
received) and 207 became
[`a064856-stirling-catalan-transforms`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a064856-stirling-catalan-transforms)
(`ea25dd768`), which proves Spiridonov's numerical model `(1.47^k + 1)A_k`
wrong as an asymptotic, credits his Conjecture 3.3 to Bauer and Golinelli
(2001), and corrects one sentence of Report 207 about Report 205. Report 163
became
[`a068598-disjoint-partition-families`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a068598-disjoint-partition-families)
(`6e53455cf`), which corrects two statements of the OEIS entry A068598 (the
graph comment counts maximal cliques; the posted fits `A exp(B n^c)`,
`c > 1`, are not asymptotic), and Report 165
[`a067590-odious-evil-partitions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a067590-odious-evil-partitions)
(`715fb82db`), which proves Kotěšovec's conjectures in A067590 and A116492
and overlaps the Thue–Morse atlas of `Analysis/FabiusFunction` in method
only. Independent checks of three writes corrected wording and figures, not
theorems: `8be867096` (a238873: the front matter's "decays like" was an upper
bound only), `45f6ef541` (a064856: the transseries volume's `h_vol = 0`
separated from Part I's `h(ρ)`) and `56d6dd98c` (a068598: Remark 3.3's Simkin
interval and a sentence on the block construction); the checks of a192563 and
a067590 are pending. No reciprocal notes were committed: the
write-time drafts find none required, and two optional pointers (into
`a082161-airy-amplitudes` and into the atlas, under its own procedure) were
not applied. Nothing was superseded; the bundle's Reports 209, 210 and
212–214 on the spectral moments `M_{2k}` remain archives in `docs/incoming`,
named as leads in the a064856 report. No manuscript refutes a repository
claim, and nothing was submitted to the OEIS.

Batch 108, thirteen archives of the bundle arrival `60f54ea06` (bundle
Reports 132, 157, 161, 164, 166–169, 184, 194, 236, 238 and 239), was placed
in one commit (`602e5bd0f`) as ten new reports and one addition, all under
`generating-functions-and-asymptotics/oeis-sequence-asymptotics/`; the
writes are pending, so the reports below are staged deliveries, described
from their delivered articles. Reports 164 (base), 161 and 166 became
[`a307030-pop-stacked-permutations`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a307030-pop-stacked-permutations):
an explicit generating function for A307030 with simple poles, infinitely
many of them positive, so the counts are not P-recursive, which proves
Claesson, Gudmundsson and Pantone's numerical predictions; Report 161's
operator proof becomes a second route, and Report 166 adds the run
statistics (A309993) and an alternate proof of their Conjecture 2, crediting
a prior proof by Patel on MathDB that the intake could not read. Report 157
became
[`a397711-bounded-indegree-dags`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a397711-bounded-indegree-dags)
(an Airy `n^(1/3)` term in `log a_n`, via the Mallein lemmas also used by
`a238873-diagonal-partitions`) and Report 167
[`a308338-nested-cycle-assemblies`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a308338-nested-cycle-assemblies).
Seven single-source matrix reports share a style but no theorem:
[`a299907-lonesum-decomposable-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a299907-lonesum-decomposable-matrices)
(Report 132),
[`a197458-line-sum-two-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a197458-line-sum-two-matrices)
(168),
[`a089479-fixed-permanent-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a089479-fixed-permanent-matrices)
(184),
[`a222959-zero-slope-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a222959-zero-slope-matrices)
(194),
[`a110058-square-contingency-tables`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a110058-square-contingency-tables)
(236),
[`a138178-symmetric-packed-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a138178-symmetric-packed-matrices)
(238, the symmetric analogue of matrix compositions, kept separate because
it answers none of that report's questions, with reciprocal notes to it and
to `a260700-parabolic-double-cosets` planned) and
[`a027832-symmetric-sign-matrices`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a027832-symmetric-sign-matrices)
(239). Report 169 was placed as Part IV of
[`a261781-matrix-compositions`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions):
it re-proves several results of Parts I and II on A261784 (second routes) and
adds a joint Gaussian–Poisson law of columns and repeated cells, which bears
on two of Part II's questions without answering them. The placement message
sets what the writes are to record: Claesson–Gudmundsson–Pantone's printed
list of positive poles omits `ρ₁₂ = 5.33887671272`; the Erlihson–Granovsky
covariance display (preprint eq. (4.54)) gives the negative variance
`3/e − 18/e²` at `p = 1, C = 3, u = 1`; Riedel's fitted exponent
`M ≈ 0.4705` "close to but not equal to 1/2" is answered by Report 167
(`M = 1/2`, `N = e^(−γ/2)`), which does not itself say so; Report 236's
claim of "an eventual square case" of the Canfield–McKay correction-factor
conjecture settles one regime, not the conjecture; Report 166's credit to
Patel stands on its own account; and the "second independent rational
implementation" promised by Report 184 and the C++ meet-in-the-middle count
cited by Report 194 are not shipped. One delivered file of Report 239 has
two stray carriage returns (the PDF prints "meven" in eq. (7.10)); it is kept
byte-for-byte by a `-text` line in `SetTheory/Cardinals/.gitattributes` and
is to be fixed at the write. The triage's "prepared for private review"
flags on Reports 236 and 239 were false positives. Not staged and
retrievable from `60f54ea06`: PDFs, member manuscripts, delivered READMEs
and checksum manifests. Nothing was superseded, and no manuscript refutes a
repository claim; there are no write, reciprocal-note or independent-check
commits yet.

Batch 114, seven of the eight archives of two "New research reports"
arrival commits of 5 October 2026 that are not part of the session bundle,
was placed in one commit (`99053b5d1`) as two additions and five new
reports. `binary_morphic_fluctuations` and
`Digit_Sum_Divisibility_in_Lacunary_Iteration` arrived in `e4d5dcf9e`, the
other five in `2399df2bd`. The batch's intake record gave
`binary_morphic_fluctuations`' arrival as `2399df2bd`;
`git show --stat e4d5dcf9e 2399df2bd` shows it in `e4d5dcf9e`, which the
report's README and article cite. The eighth archive, `Periodic_Rounding_Extinction`
(`e4d5dcf9e`), continues `a082528-rounding-extinction`, the host of bundle
cluster 110-A082528, and is held for batch 110 so that the host gets one
write; it was not placed. `binary_morphic_fluctuations` became Part III of
[`binary-substitution-discrepancy`](generating-functions-and-asymptotics/binary-substitution-discrepancy)
(`788a7bd5a`), which answers Part II's research question 7 on the unbounded
regimes of `0 → 1, 1 → 1 0^a 1^b`: the cluster set `±(a−1)/(2 log a)` of
`(#0 − #1)/log N` at `a = b+2`, a closed-form supercritical interval for
`a ≥ b+3` (`±√10`, with `X(N)² + 5X(N) ≤ 10N` at every prefix, for
`(a,b) = (8,1)`), and exact histogram, Gaussian, local and large-deviation
laws for every critical arrangement, its zero-height profiles counted by
A001787. `Digit_Sum_Divisibility_in_Lacunary_Iteration` became Part II of
[`a168362-lacunary-iterates-mod4`](congruences-and-valuations/iterated-series/a168362-lacunary-iterates-mod4)
(`42d31831e`): `v_p ≥ (s_p(N) − 1)/(p − 1)` for every coefficient of every
integer iterate of `Σ x^{p^j}`, inverse iterates included, which answers
Part I's question 13.2; `[x^{2p−1}] F_p(F_p(x)) = p` shows Part I's
suggested odd-prime cutoff "digit sum at most two" (question 13.3) false, a
re-scoped question, not a retraction; three Part I results re-proved at
`p = 2` are printed as second routes. The other five opened reports in
`ordinals-and-order-types/`, the collection's set-theory and logic
category, each from one manuscript; they share a delivery template but no
theorem and no citation: [`random-bits-arithmetic-cuts`](ordinals-and-order-types/random-bits-arithmetic-cuts)
(`90198e982`; coding cuts of random predicates on countable models of PA,
Boolean spectra, three induction regimes, finite catalogs),
[`noisy-parity-cubes`](ordinals-and-order-types/noisy-parity-cubes)
(`b7d0d5e96`; it re-proves two classical lemmas of Part IV of
`measurable-box-games`, printed as second routes),
[`robust-neutral-choice`](ordinals-and-order-types/robust-neutral-choice)
(`9ccf04eae`),
[`freiling-symmetry-blacklists`](ordinals-and-order-types/freiling-symmetry-blacklists)
(`bf70d7db4`) and
[`bounded-width-power-set-compression`](ordinals-and-order-types/bounded-width-power-set-compression)
(`74a988c32`), whose source's antichain-transfer theorem is false as
printed for non-injective codes: the write prints the counterexample and the
repair as Remark 9.10, and the ZFC classification stands. Reciprocal notes
went to `naming-elementary-embeddings` (a shared Glazer–Yao citation),
`measurable-box-games` and `noisy-parity-cubes` (`ae36f0190`); the
same-batch "see also" lines were written with the reports. Every write was
independently checked. `19cdaf73c` (robust-neutral-choice), `c71217525`
(bounded-width) and `cf0e8e46f` (noisy-parity) needed no correction;
`bf04031ba` showed, with Jech's Theorem 7.16, that `SAP_1` is strictly
stronger than choice for pairs; `4b519a0b9` completed random-bits'
formal-status paragraph with the same-named no-finite-model copies in the
unimported `Optimizations/Logic_Foundations_Optimizations.lean`. Two checks
found errors in earlier repository text, corrected under the standing rule
with dated notes: `b5df007e4` restored eleven `C → Ĉ` renames that the
batch-73O1 write had missed in Part II of binary-substitution-discrepancy
(its bound (13.9) for A284369 printed `E_0 < 2.1547`; `E_0` reaches 3.6437
and the sharp bound is `2 + √3`), and `cbc7a553b` found Part I's formula
(16) of a168362 false with its first binomial read as an integer and right
read mod 2, the reading its classification uses. The random-bits report
cites `Logic/PeanoArithmetic/NotFinitelyAxiomatizable` and
`Logic/PeanoArithmetic/ListCoding`, and robust-neutral-choice the
Cardinals Lean library's `GenericErgodicity.lean`; their READMEs gain
pointers in this catalogue, and none of the batch's theorems is
formalized. Nothing was superseded, no manuscript refutes a repository
claim, and nothing was submitted to the OEIS.

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
