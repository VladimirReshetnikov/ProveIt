# Independent mathematical review of the refinement manuscript

Reviewed the working manuscript in
`output/sat_rectangular_refinement_2026-10-26/`, especially
`sections/interface.tex`, `matrix.tex`, `certificates.tex`, `schedule.tex`,
`outcome.tex`, and the relevant parts of `barriers.tex`. Also read the frozen
finite data, verifier, and interval outputs in
`research_incoming_improvement/deliverable/` and the accompanying proof note.
This note records mathematical/source review, not a local Lean rebuild or an
implementation of the full SAT algorithm.

## Actual issues found and repaired

1. **Description-length factor under recursion.** The first draft put
   `poly(s+L)` at every recursion level and then absorbed the product into an
   `O(lambda log lambda)` exponent. This is unjustified for unrestricted `L`:
   literal unrolling gives `(s+L)^{O(log lambda)}`. The interface now separates
   normalized computational work from a single fixed polynomial cost factor
   for access to original descriptions. Allocation counts, generated-mode
   loops, and generated arithmetic depend on `s`, whereas the promised fixed
   polynomial source-entry cost is paid per source-access event. Immutable
   references avoid expanding/copying descriptions. Input-offset lookup can
   be implemented by an `O(L)` scan when random-access input is unavailable;
   this is a per-event cost, not recursion fan-out. The recurrence is now for
   normalized work with `poly(s)` per level, and the schedule restores the
   single `P(s+L)` factor afterward. No restriction `L=poly(s)` was added.

2. **Incorrect final displayed decimal digits.** Exploratory binary-floating
   calculations produced a few erroneous last digits. Exact interval output
   gives

   - `C_T = 28.433739378341669141570416862796860317565...`;
   - `C_S = 28.305780030299756871693657710058104959257...`;
   - old-backend triple coefficient
     `29.776818945083746990260975450513679978306...`.

   The schedule's branch table now uses twelve correct digits after the
   decimal point. Safe eventual coefficients `28.434`, `28.306`, and `29.777`
   were never affected. The root author was notified to update any other
   headline occurrences.

3. **Algebraic-descent support wording.** Polynomial equations guarantee the
   same permitted coefficient positions and no increase in rank. They do not
   by themselves force an originally nonzero coefficient to remain nonzero.
   The lemma now says "same permitted bilinear support ... and no larger
   rank." Vanishing coefficients are harmless for every cost bound here.

4. Fixed two literal missing backslashes before `quad` in the schedule and
   removed a stray incomplete final sentence from `matrix.tex`.

Only the three manuscript files `interface.tex`, `matrix.tex`, and
`schedule.tex` were edited by this reviewer. Other findings were sent to the
root author.

## Mathematical checks that passed

### Exact contraction interface and support accounting

- The stated entropy normalization is consistent: precision constant `6`,
  family multiplicity `2/r^2`, and mode-product constant `pi^2/24` yield
  `kappa = pi sqrt(2)/ln(2)`.
- Passing from directed pair entropies to unordered-pair entropies requires
  a factor `sqrt(2)`; both the proof and all beta-squared formulas include it.
- Singleton tables are paid by `alpha_r = sqrt(2(r-1))/r` recursive entry
  evaluations. They are not treated as free coefficient oracles.
- A three-block plan has `r-3` internal merges and one final triangle. Its
  supports include every operation and the input/output branch. Every
  singleton or intermediate boundary array is an input or output of one of
  these operations, so the same selected-plan bound covers local storage.
- Exact mode-list cardinalities and selector products have polynomially many
  bits in the root parameter. A fixed finite plan menu and fixed integer
  coefficient scale therefore permit exact selection without floating-point
  logarithm comparisons or a counting oracle.

### Fixed matrix library and bit complexity

- Endpoint interpolation with thin ratio `1/2` and square exponent `9/4`
  yields, for sorted `x>=y>=z`,
  `max((1+eps/2)(x+y), x+(3/4+eps)y+z/2)` with `eps=10^-5`.
  The thin and square slacks are both charged. A zero-slack finite algorithm
  is not assumed.
- The interpolation scales `2(y-z)` and `2z-y` are nonnegative in the thick
  region and sum to `y`. In the thin region, padding the inner dimension to
  `y/2` costs at most the displayed input/output branch.
- Two fixed finite bilinear bases suffice. Rounding tensor iteration counts
  causes constant dimension factors. The same fixed coefficient field and
  fixed exceptional primes work for all recursive matrix shapes.
- Weak Nullstellensatz descent, an integral primitive element, and reduction
  in `F_q[T]/(g)` are valid. Irreducibility or separability modulo `q` is not
  needed for the division-free identities. Excluding primes dividing fixed
  scalar denominators is sufficient.
- The CRT transfer correctly lifts *coordinate integer products* before
  restoring the multiplication table of `R_p`. It does not incorrectly use
  a homomorphism `R_p -> F_q`. Integer-product bit lengths and the number of
  coordinate pairs/primes are polynomial in the root parameter.
- Sequential coordinate pairs and primes, together with depth-first finite
  bilinear recursion, preserve a polynomial factor times largest-array
  storage. An arithmetic exponent alone would not establish this; the
  manuscript supplies the required schedule.

The more detailed bridge audit is in `audit_formal/matrix_bridge_audit.md`.

### General subset certificate and triple specialization

For `k`-subsets, each diagonal term occurs `C(q-1,k-1)` times and each
cross term occurs `C(q-2,k-2)` times. Multiplication of each subset cross
sum by `2(q-1)/(k-1)` gives precisely the required factor `2` after
normalization. Consequently the manuscript's `U_k` is a valid upper bound
for the squared norm of every weighted average of selected supports.

Choosing one maximizing support for each plan at the actual entropy vector
makes the minimum plan cost at most the weighted-average cost; Cauchy--Schwarz
and the directed-to-undirected factor give
`beta_k^2 = 2 U_k/(L_*^2 r^2)`. This proof does not assume simultaneously
realizable maximizers for different subsets.

For `q=9,k=3`, the cross coefficient is `8`, denominator is `28 W^2`,
and all `C(9,3) 72^3 = 31,352,832` support triples are covered. The integer
coefficient triples in the manuscript agree with both the old and new
rectangular envelopes. The old-backend comparison really keeps the same
plans, weights, backend, and schedule.

### Full schedule, uniform errors, and storage

- The taper sum equals the listed rational caps, with infinite tail cap
  `0.0499999`. Every root, retained-side, fresh-side, and rounding packing
  condition has a fixed strictly positive power margin.
- The provisional tail depth `log_(20/11)(lambda)+O(1)` is noncircular:
  `63/100>11/20` makes the smallest taper grow as a positive power of
  `lambda`, so packing is valid throughout the provisional range; the
  resulting actual tail child ratio is below `11/20`.
- The `6 log_2(lambda)` precision guard bounds the creation-precision ratio
  by `O(lambda^4 2^-B)=o(1)`. Floors, additive guards, the fixed power gaps,
  and `lambda^-3` padding are consistent with uniform estimates on the
  `O(log lambda)` active levels.
- The listed masses follow successive factors `2/r`. The tail contribution
  ratio is `gamma=5/sqrt(63)<1`. The infinite cache branch exceeds every
  finite aggregation branch, and the root is the largest local storage
  branch. The exact radical expressions reproduce the interval outputs.
- Ancestor and descendant arrays add in size; with only `O(log lambda)`
  active frames this gives a maximum of local leading space coefficients,
  not a sum of them. Polynomial CRT and bit overheads do not change it.
- Source entry, packet entry, direct-leaf, and normalized per-depth
  polynomial work are lower order on `s/sqrt(lambda)`.

### Rational checker review

Read the complete standalone verifier. Its support reconstruction uses
bitsets and midpoint merges, with exact Python integers for all Gram
matrices and maxima. The pair and triple normalization agrees with the
proved theorem. The checks use explicit exceptions, not removable Python
`assert` statements.

The transcendental enclosures are valid: Machin's formula with alternating
arctangent remainders encloses `pi`; the positive `atanh(1/3)` series and a
geometric remainder enclose `ln(2)`; integer square roots give certified
rational square-root intervals. All accepted coefficient comparisons use
these rational intervals. Reading their endpoints with high-precision
decimal arithmetic independently confirmed the corrected digits above.
The recorded ordinary and `-O` results agree. Another team reviewer is
performing the independent finite support reconstruction/replay, so this
note does not claim that simply reading that result is a second independent
implementation.

## Scope and remaining limitations

No further structural mathematical error was found in the new certificate,
the fixed matrix bridge, or the paid schedule after the repairs above.
This conclusion remains relative to the explicitly imported Cauchy,
Hermite, packing, immutable-entry, and 3-SAT reduction interfaces.

The result improves a leading coefficient of a generic normalized wire
bound. It does not improve the logarithmic denominator power, establish a
universal best constant per SAT variable, dominate the separate incoming
low-memory point, or compare actual implementations. The report correctly
keeps these limitations explicit.

The finite crossing-rank probes use all partition labels and a fixed small
range. Their full ranks modulo a prime imply full rational rank of those
integer matrices, but do not prove any asymptotic image-rank theorem or a
claim about every binary-label submatrix. The rectangular-grid minimax
lemma is a restricted information-bound obstruction, not a SAT lower bound.

The upstream formal 3-SAT result was inspected at its pinned commit and its
reported successful kernel/comparator job; no local Lean rebuild of that
result or formalization of the present new theorem has been performed.
