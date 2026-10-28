# Independent iteration-3 component audit

## Scope and outcome

This audit covers the newly authored mixed-order projective coefficient kernel,
its affine adapter and precision-doubling root construction, the array-factorized
and sparse-factorized matching-potential implementations, and the degree-0.51 polynomial-space schedule
composition. It is a mathematical/code review plus finite exact checks, **not**
a formal verification of the upstream ETH manuscript or a complete SAT solver
run. No program from an incoming archive was imported or executed.

No blocking algebraic or implementation defect was found in these components.
The most important review correction was a benchmark improvement: the matching
dense comparator initially recomputed row sums. The author replaced that with
maintained exact row sums and reran the checks and measurements. Only the final
cached-row comparator ledger is authoritative; provisional larger speedups are
superseded.

The later sparse-factorized extension was separately audited against the final
source and three-method benchmark. Its positive-support idea is credited to prior
work; the new contribution is the exact two-phase matching-potential composition.

## Projective extraction

- The quotient is the free integral module given by
  `Z[U,V]/(U^4+U+1,V^ell)`, reduced modulo `2^p`. The quartic is irreducible modulo
  two: it has no binary root and has remainder one modulo `U^2+U+1`. The explicit
  residue U has order 15. Nilpotent V does not require enlarging this ring.
- For a surviving character monomial, every free exponent is
  `alpha_j=beta_j+q_j m_j`, with `m_j>=0` because `q_j>beta_j`. With a minimum-target
  pivot, every `q_j>beta_k`, so homogeneity forces all `m_j=0`. This excludes
  projective aliasing. The available-order pivot-swap argument is correct; it is
  an implementation selection observation, not a new coefficient formula.
- Orders 3 and 5 and the grid-cardinality inverse are odd units. Root order alone
  is not used as a substitute for orthogonality: both character families are
  checked explicitly. Zero-target coordinates are dropped; empty and singleton
  cases correctly avoid unnecessary root work.
- For precision doubling, put `e=x^15-1`, divisible by `2^k`. Then
  `x'=x(1-e/15)` gives `(x')^15=(1+e)(1-e/15)^15=1+O(e^2)`.
  Thus precision `min(2k,p)` is valid in this commutative quotient, including
  nilpotents. Only scalar 15 is inverted. The preserved bitwise lift provides a
  separate precision schedule for regression checks. This is classical Newton
  lifting, not a new mathematical identity.
- Input coordinates are canonicalized at creation precision before both
  projective and centered extraction. The anisotropic antipodal baseline uses
  the correct guard valuation `v2(prod beta!)+sum_odd beta_j-1`. Its numerator is
  formed at that many extra bits, checked for divisibility, shifted, and divided
  only by an odd factorial part. The all-even center contributes zero for
  positive total degree, justifying the floor-half-grid count.
- The reflected Gray code visits the exact product grid, changing one coordinate
  by one step; signed neighboring-root increments and phase updates agree with
  that movement. Unit radices arising in antipodal boxes are handled correctly;
  empty and single-target extraction paths are handled separately. The affine
  adapter correctly homogenizes the constant target
  to `R-|beta|`, or returns zero when the requested degree exceeds R.
- The theorem is explicitly inherited. The fixed-rank prototype does not
  implement arbitrary upstream source-ring embeddings; finding and representing
  roots in those rings remains a charged integration task. The demonstration
  dispatcher is not a replacement for all inherited sign/cube or other kernels.

## Matching factorization

For all-left-then-all-right assignment order, each matching table really factors
as `s_j x_ja B_jab`, with `s=t^(-h)d^U`, `x=c^L`, `B=t^C`, and positive rational
`d=1+1/(eta Q^2)`, `c=1+1/(eta Q)`, `t=1+1/eta`.

The left update removes one d from the common scale and places one c in the
chosen row factor. The right update removes one c from the known left row and
places one t in the chosen cell. Maintained row sums and weighted total therefore
give the exact conditional candidate values. Multiplying the stored matching
products is legitimate because edges in each matching have disjoint endpoints.
Parallel input edges are placed in distinct matchings; left and right endpoint
names are tagged separately even when their raw identifiers coincide.

All divisions are by positive rationals c and d, never by a possibly zero table
entry or nonunit residue-ring element. The exact averaging check and smallest
label tie rule are preserved. The implementation sorts tagged vertices; endpoint
identifiers must be mutually sortable within each side, as in the integer-ID
fixtures. No arbitrary interleaved assignment-order claim is made.

Each incident edge needs Q candidate corrections and constant post-selection
state work, giving **O(MQ+VQ) rational update operations**. Sparse B starts at the
implicit value one, and each completed edge creates at most one cell. Hence
potential-state storage is **O(KQ+min(M,KQ^2))** rational values. This excludes
graph/incident storage, traces, optional candidate traces, and the returned
**Theta(Q^2)** dense load matrix. First-fit matching coloring O(MK), sorting,
initial powers and rational bit costs remain charged. This is a distinct
matching-potential refinement, not a re-claim of previous sparse column scoring
or asymmetric packing.

### Sparse positive-support extension

During the left phase B is identically one. After replacing an incident scale by
`s'=s/d`, the candidate-dependent contribution is `s'(c-1)Q x_a`. Removing the
label-independent unit baseline leaves `s'(c-1)Q(x_a-1)`. During the right phase,
after replacing the known row factor by `x'=x/c`, the analogous delta is
`s x'(t-1)(B_ab-1)`. All stored x and B values strictly exceed one; weights are
strictly positive exact rationals, so every stored score contribution is positive.

Conditional averaging gives the exact candidate potential
`Phi_current + delta_candidate - sum(delta)/Q`. Thus, if any label is absent from
the score dictionary, the least absent label is the unique tie-rule choice among
zero deltas. If all Q labels occur, minimizing `(delta,label)` is exact. An absent
label is found with at most the number of stored scores plus one probes, not an
unconditional Q scan. The chosen potential formula is an exact identity, not an
approximation or a test-only replacement for the conditional expectations.

At each right endpoint, its remaining edge count is positive before decrement;
division by c leaves x at least one. Deleting exactly when it returns to one is
correct. Each nondefault x entry is witnessed by a remaining half-assigned edge,
and each B entry by a completed edge. Consequently potential-state storage is
**O(K+M)** rational values, including sparse temporary scores, not O(KQ). The
unchanged dense output and optional all-candidate vectors remain excluded and
explicitly charged. The ordinary selected-trace interface has support-sensitive
work

`O(M+V + sum_left sum_incident |support(x_j)| + sum_right sum_incident |support(B_ja)|)`.

This is at most the prior O(MQ+VQ) update order, not a smaller worst-case Q order.
The result relies on all-left-then-all-right processing. At completion all x
dictionaries are empty and `sum_j s_j[Q^2+sum(B_jab-1)]` independently reconstructs
the final potential. Every dictionary/default/deletion and exact-potential
invariant checked in the saturated-state audit agrees with this proof.

## Independent test design

`check_components_independent.py` does not reuse the production coefficient DP
or matching conditional-product oracle:

- Its coefficient oracle convolves sparse polynomials over unrestricted integers,
  reduces `U^4=-U-1` and `V^ell=0`, and only then reduces final coordinates modulo
  `2^p`. This tests ring arithmetic independently of `Ring.mul`.
- Its affine oracle directly multiplies affine forms with constant transitions,
  rather than using the production homogenization construction.
- Its matching oracle enumerates all complete labelings and directly computes
  the final exponential load potential; prefix averages independently determine
  every conditional candidate value, selected tie and trace for all three
  maintained methods. Sparse selected-only output is also checked separately.
- A separate observer of the actual sparse execution reconstructs U, L and C
  directly from every selected assignment prefix in a filled-support fixture;
  it does not modify production code or reuse stored factors as its oracle.
- It checks primitive and proper-order fifteenth-root powers, non-power-of-two
  precisions through 257 bits, nilpotent lengths through three, and exhaustively
  checks available-order pivot counts on 1,364 profiles.
- It recomputes all recorded benchmark medians/counts, checks implementation and
  benchmark-script hashes where supplied, and rejects changes to audited source
  during a run.

Final exact run receipts are `independent_components.json` and
`independent_components_optimized.json`; they contain the audited SHA-256 values.
Primary author test suites were also independently replayed, with receipts under
`replay_mixed*.json` and `replay_matching*.json`.

The separate audit passed **180** integer quotient products, **18** high-precision
root/property/bitwise-versus-doubling comparisons, **176** homogeneous outputs,
**214** affine outputs, **7** proper-order root rejections, and **1,364** pivot
profiles. Its **126** matching instances enumerate **2,400** complete labelings
and check **744** conditional candidate values against each of three maintained
methods (**2,232** method/value equalities). The saturated **M=256, Q=8** case
checks all **512** selected-prefix states, including **440** full-support and
**72** absent-support choices. It reaches **8** x entries and **64** B cells and
finishes with load four in every cell. Final ledgers contain **8** mixed
and **11** matching benchmark fixtures. The same checks pass under `python -O`;
they use explicit exceptions rather than removable `assert` statements.

## Benchmark interpretation

The mixed and common-root paths use identical ring dimension, creation precision,
input representatives, Gray machinery, validation and extraction charges. The
centered comparator is the stronger anisotropic antipodal implementation, not a
weaker uniform-step variant. Cached-root and fresh-root measurements are separate,
and both fresh common and fresh mixed paths charge the same root construction.
These are explicit implementations, not proofs of optimality over every possible
common-root or centered implementation.

The final matching benchmark includes dense entries **and maintained row sums**,
array factorization, and sparse factorization. Coloring, initialization, each
method's invariant checks, selected traces and dense output are charged in all
three. Sparse averaging is symbolic rather than materializing unrequested full
candidate vectors; those vectors are separately verified in correctness tests.
The dense reference has update order O(MQ^2+VQ), not full-potential recomputation.
The stronger array-factorized method is the primary comparator for the added
sparse step. Final sparse-over-array wall ratios are **1.91–3.87x** on random
fixtures, **4.79x** on parallel edges, **2.04x** on the 96-edge single matching,
and **1.576x** on the filled 256-edge/Q=8 control (**1.503x CPU**). All 64 cells
in the latter genuinely become positive. The array method itself still has
regressions against dense: about **0.965x** on tiny Q=1 and **0.936x** on random
M=16/Q=2. No sparse regression appeared in these eleven selected fixtures, which
does not imply universal dominance. Raw wall/CPU samples and both source/script
hashes are preserved, with start/end stability assertions. Earlier two-method
measurements remain historical ablations, not current headline numbers.

Both suites use five repetitions on a shared executor and rotate/alternate
methods. These selected synthetic component results are noisy, do not establish
statistical significance or a universal wall-clock crossover, and are not
end-to-end SAT speedups. On the six selected mixed-even final fixtures, the
fresh-root mixed path is **1.34–4.67x** faster than the fresh common path and
**1.005–1.68x** faster than the anisotropic path; **1.005x is effectively a tie**
at this measurement quality. On eight target-one coordinates it is about **24x
slower** than anisotropic extraction. Equal-order all-four comparisons have no
mixed-radix structural advantage. Final mixed-kernel timings and regressions
belong to the final source-hashed ledger; earlier ledgers must not be mixed with
it.

## Degree-0.51 schedule composition

The new prefix uses arities `(16,16,8,6,5,4,4)`, then arity 3 with taper ratio 3/4.
The independently checked leading masses are
`1,1/8,1/64,1/256,1/768,1/1920,1/3840`, followed by `1/7680`.
The full taper budget is exactly 239/1000. The root degree gate is
`.51+8(.06124)=.99992`, and depth-one rounding is `9(.1111)=.9999`.
All later retained-degree, rounding and fresh-side gates have strictly positive
rational margins. Generated degree exponent .239 stays below the inherited .51
cap. Since `2/3<7/10<3/4`, the proposed depth bootstrap and divergent minimum tail
taper are compatible. With the stated leaf threshold, leaf and packet-entry costs
remain lower order under the imported recursive interfaces.

`check_degree051_independent.py` uses its own rational arithmetic and a different
pi identity, `pi=4(atan(1/2)+atan(1/3))`, to enclose the paid infinite coefficient:

`21.139416167998583798725141 < C < 21.139416167998583798725142`.

It passes normally and under `-O`; the safe eventual coefficient **21.14** is
therefore numerically and gate-wise justified **assuming** the inherited adaptive
flag lemma and recursive degree/precision/packing interfaces. This remains a
stronger-degree-assumption bound on normalized wires, not a generic SAT-variable
bound or a smaller logarithmic order. The other matrix/schedule certificates are
outside this component audit except where separately reviewed by their owners.
