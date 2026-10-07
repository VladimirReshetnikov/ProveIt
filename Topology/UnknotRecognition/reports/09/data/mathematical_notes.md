# Direct reduced scanning and safe early termination

## Scope and status

The canonical implementation is `fast/fastunknot/reduced_scan.py`. It is an
opt-in engine, not a replacement justified on every input. The mathematics
uses the standard pointed/reduced Khovanov construction; the useful contribution
here is its implementation in the existing local scanner, a basepoint placement
lemma that avoids an observed width regression, and a decision-only early-stop
criterion. None of these results establishes general quasi-polynomial time.

The baseline is upstream commit
`4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711`.

## Pointed quotient category

Write `A = F2[x]/(x^2)`. Cut one diagram edge into two permanent boundary
endpoints. Choose one endpoint `p` as distinguished. Each crossingless matching
has an arc through `p`, and every basis of `Hom(a,b)` has one circle of the
overlay `a union reflected(b)` through `p`. Dots on that circle give the
central boundary action of `x`. Quotient every morphism space by the image of
this action. The dot-sliding relation makes these images a two-sided ideal:
composition and subsequent gluing commute with the fixed boundary dot.

The quotient is therefore an additive category and the quotient map an
additive functor. Chain homotopies and inverse morphisms remain chain
homotopies and inverse morphisms after applying it. In particular, all of the
scanner's earlier cancellations are valid. If the marked endpoint appears
partway through the scan, the earlier scan takes place in the ordinary
category, and the quotient is applied immediately after the crossing that
introduces the endpoint. This is the image of the previously computed complex
under an additive functor; it does not require rescanning its prefix.

For a Hom basis with `k` circles, the pointed quotient has basis the monomials
in the other `k-1` dot variables and dimension `2^(k-1)`. The distinguished
endpoint receives a fresh label smaller than every original label. The existing
circle numbering therefore makes its circle index zero. A quotient monomial
is encoded by deleting this zero bit, giving exactly half as many coefficient
bits as the unpointed Hom space for the same pair of pointed matchings.

### Exact surface rule

An ordinary connected genus-zero component with boundary circles `B` evaluates
without dots as

`sum_(j in B) product_(i in B minus {j}) x_i`,

and with one dot as `product_(i in B) x_i`. Two dots give zero. Positive genus
also gives zero over F2 in this dotted theory. If the component contains the
distinguished output circle `p`, quotienting by `x_p` leaves:

* with zero dots: `product_(i in B minus {p}) x_i`;
* with one or more dots: zero.

Unmarked components retain the ordinary rule. This is exactly
`evaluate_pointed`. Components retain their original topological Euler
characteristics; only their dot-variable masks and evaluation change. When
the endpoint first appears, input masks have not yet been compressed; the
compiler explicitly distinguishes that stage from later pointed stages.

For an object with `m` arcs, its endomorphism ring after quotient is
`F2[x_2,...,x_m]/(x_2^2,...,x_m^2)`. A polynomial is invertible precisely when
its constant coefficient is one. Every such unit is its own inverse. Thus
the existing cancellation tests and identity shortcuts remain valid.

The two cut endpoints are the only frontier after the last crossing. There
is then a unique matching, whose endomorphism ring in the quotient is F2.
After scalar cancellation the remaining object count is the reduced rank.
Closing the cut turns the marked arc into the marked circle, with its factor
`A/(x)`. This is the usual reduced complex. The alternative convention `xA`
is isomorphic to `A/(x)` by `1 -> x`, apart from a quantum grading shift; this
engine records only the unchanged homological grading.

## Why the basepoint must close late

Fix an order of `n` crossings. Choose an edge whose second occurrence lies in
the final crossing. Let its first occurrence be at position `a`. Split its
two occurrences into labels `p` and `q`, placing the mark at the first one.
For every proper prefix, the cut frontier has exactly the same cardinality
as the original frontier. Before `a` they agree; from `a` through `n-1`, one
frontier label is merely renamed. At the end the original frontier is empty
and the cut frontier consists of `p,q`. Hence

`w_cut <= max(w_original, 2)`.

The implementation picks, among the edges of the last crossing, the one whose
first occurrence is earliest. This maximizes the duration of the pointed
quotient without adding a frontier endpoint before closure. It is a policy,
not a theorem about minimum running time or minimum intermediate multiplicity.

An arbitrary early-closing cut instead adds two permanent frontier endpoints
after its second occurrence. This seemingly harmless change was disastrous
on `stress_braid5_36`: a first-crossing cut required 2,127,039 compositions and
35,193 peak objects, compared with 23,710 compositions and 17,694 peak objects
in the baseline. The last-crossing policy reduced these figures to 16,705
and 12,341. These are measurements, not universal inequalities.

## An exact decision-only lower bound

**Isolated summand theorem.** At any stage, suppose the partial scanned complex
contains `s` objects with no incoming or outgoing nonzero differential entries.
For a validated one-component input diagram, the final reduced Khovanov rank
is at least `s`.

**Proof.** Each isolated object is a one-term direct summand of the partial
complex, with a homological and possibly quantum grading shift. Gluing the
remaining tangle is additive, as are delooping and the pointed quotient.
Therefore the completed complex contains the direct sum of the completed
isolated summands, up to chain homotopy. Each completed matching is the reduced
Khovanov complex of a nonempty classical link: the marked edge is present
either in the current pointed tangle or in the as-yet unprocessed complement.
The reduced Khovanov homology of a link with `ell >= 1` components is nonzero.
For example, its graded Euler characteristic is the reduced Jones polynomial;
at quantum parameter one its absolute value is `2^(ell-1)`. This is an integer
Euler characteristic of dimensions, not a reduction of that integer modulo
two. Thus each completed summand contributes at least one to the total
dimension. Dimensions add under direct sums. QED.

Consequently `s >= 2` proves the input is knotted by the reduced-rank unknot
detection theorem. There is no corresponding early unknot inference from
`s=0` or `s=1`. Unfinished scan sizes, numbers of matchings, and resource-limit
events are not lower bounds on the final homology.

The decision API inspects every completed intermediate stage, and inspects
the final transfer before its scalar cancellation. It stops after finding
two isolated objects. Its result contains `reduced_rank=None`, `lower_bound=2`,
the stage, remaining crossing count, the marked edge and scan order, and two
object IDs with matching and degree data. This is **replay data**, not a small
independently checkable topological certificate: verifying the preceding
chain reductions still requires replaying the scanner, unless a separate
chain-equivalence witness is supplied.

Natural-order Conway connected sums provide an explicit before-closure test:
two, three and eight summands terminate after the first 11 crossings, leaving
11, 22 and 77 crossings respectively. The baseline's visible factorization
already handles this family efficiently. These examples verify that the new
decision engine can stop before full homology; they do not establish a new
asymptotic advantage over the full existing recognition pipeline on this
particular family. The supplied prime examples generally trigger only at the
final transfer.

## Verification and performance record

`test_reduced.py` checks the quotient composition formula on every polynomial
input for all triples of noncrossing matchings on at most six endpoints,
checks known ranks and shape-cache equivalence, verifies the frontier lemma,
tests budget semantics, and replays a before-closure early result.

The portable exhaustive script evaluates every signed two-strand braid word
of lengths 1, 3, 5 and three-strand word of lengths 2, 4, 6 that closes to a
knot: 2,898 diagrams. Each is compared to the pre-existing independent dense
reduced cube oracle. Additional tests cover all basepoint edges under three
orders on the smaller diagrams, for 5,052 such scans; there are 8,002 rank
scans overall. Every intermediate differential is checked to square to zero.
The final version additionally tests the separate decision API against all
2,898 independent dense ranks. See `reduced_validation.json` for exact counts.

The timing experiment uses the same precomputed crossing order for both
engines. Each randomized block contains two full baseline runs and two direct
reduced runs. Ratios are the quotient of their geometric means; confidence
intervals are bootstrap intervals for the median paired ratio. A/A ratios
show the noise in the baseline repetitions. The full raw samples are retained. The final packaged-engine run is
`reduced_benchmark_final.json`; it includes source snapshots captured before
timing, SHA256 hashes, input PDs, and the actual randomized order of every
block. The earlier `reduced_benchmark.json` is retained as a development
prototype record, with explicit metadata stating that its source was not
hashed before the run and its job orders were not recorded.
These are scanner measurements; many named knots are decided by the earlier
polynomial filters in the complete pipeline.

Nine cases were measured. On the large stress closure the median ratio is
0.723 (95% bootstrap interval 0.673--0.780). On one genuine 16-crossing
scan-decided unknot survivor it is 0.921 (0.896--0.969). There is no measurable
benefit on several small cases, and measured regressions on another survivor,
T(3,11), and the small hard-unknot example. The marked algebra saves objects
and coefficients but costs additional Python bookkeeping. The evidence
supports keeping the engine **opt-in**, not choosing it for every input.

## Complexity implications and open directions

Pointed Hom dimensions remain exponential in frontier width. Full reduced
homology can itself have exponentially many generators, so quotienting one
dot variable does not remove the output-size obstruction. A conservative
bound for the explicit scanner remains polynomial in the crossing count,
peak live-object count and `2^w`. A quasi-polynomial theorem needs a new bound
on the relevant intermediate multiplicities or a decision-only representation
that provably avoids them.

Useful next questions are: characterize families where isolated summands must
appear early; detect larger direct summands with efficiently certified nonzero
closure homology; bound certificate-finding time independently of total rank;
choose a late-closing basepoint using information beyond first occurrence;
remove the duplicate plan conversion through a compiled pointed evaluator;
and test a combined operation-count and width predictor before enabling this
engine automatically. Each would address a remaining demonstrated cost or a
precise missing theorem.
