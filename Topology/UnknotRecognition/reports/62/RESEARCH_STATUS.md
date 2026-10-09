# Research status and proof obligations

## Proved in the article

- **Sparse nonnegative zeta recovery:** at most `r*s` logical queries, no prior
  sparsity bound; every atom and final completeness follow by induction.
- **Unweighted coning reduction:** each zeta value is the baseline count or one
  coned count minus one. The identity is inherited from the maintained approach;
  its proof is included for the new contract.
- **Explicit signature-support bound:** with `B = max(1, ceil(log2(N+1)))` and
  `Q = 1 + 5*k*k*(B+2)`, support is at most
  `min(N, 2**r, Q*(2*M + 4*Q + 2*k + 2))` for positive `N`.
  This is a conservative corollary of classical AHT cycle and weighted-breakpoint
  estimates, not a new foundational weighted-orbit theorem.
- **Polynomial local marked-incidence primitive:** combine the support estimate
  with output-sensitive recovery and the unweighted AHT bound. Ports must be
  explicit finite interval lists; no succinct-grammar input claim is made.
- **Independent sparse certificate:** positive atom masses, one dominating zero
  witness per present label, and total mass conservation establish the full
  histogram without replaying search or expanding the Boolean lattice.
- **Certificate pruning:** unsuccessful deletions and final support values
  suffice; unused successful intermediate queries need not be retained.
- **Singleton-family exact costs:** `1+r*(r+1)//2` orbit calls and `2*r-1`
  retained coned proofs, for positive empty/singleton support and disjoint,
  nonempty ports under this union-keyed implementation.
- **Signature-resolved parity consistency:** the lifted histogram `d` and base
  histogram `b` give consistent counts `d-b` and inconsistent counts `2*b-d`.
- **Gluing obstruction:** equal incidence and equal per-port multiplicities can
  yield different orbit counts under the same later attachment.

## Inherited facts, not novelty claims

Classical AHT supplies polynomial unweighted and weighted orbit algorithms.
The maintained repository supplies coning, the unchanged optimized unweighted
kernel, and its independent local verifier. Nonnegative additive-query learning
is an established area; no literature-priority or optimal-query claim is made for
the elementary greedy routine. The four upstream source files are byte-identical
at the stated Git blob identifiers.

## Executed evidence

Thirty-six focused test methods pass on CPython 3.13.5. The structured summary
records 6,654 exhaustive generic histograms, 1,000 literal interval systems,
300 native dense comparisons, and 300 independently checked parity systems.
The full repository suite was not executed. No Lean/Isabelle formalization was
produced.

The final benchmark has 242 measured arm-round records and 38 warmup records;
batching represents 4,354 measured and 630 warmup calls. All these calls completed.
An earlier 200-second harness-limited attempt is separately logged and excluded.
The negative full-support results and A/A control discrepancies are retained.
There are no new whole-knot benchmark results in this package.

## Remaining obligations for a global recognition theorem

1. Bind diagrams, exteriors, encoded surfaces, orientation labels, and ports by
   independently checked geometric provenance.
2. Retain attachment-compatible data: the sparse incidence table is insufficient
   even for the four-point relation example.
3. Construct and certify compressed cuts and hierarchy updates without expanding
   represented surfaces or silently expanding succinct port descriptions.
4. Bound state bit lengths, construction costs, branching, retries, hierarchy
   length, and pattern complexity in terms of the original recognition input.
5. Prove complete surface discovery/search, not merely checking of supplied data.
6. Run full integration tests and complete recognizer ablations on native inputs.

The article gives a conditional cost-composition statement with these parameters.
It does not establish a general quasi-polynomial unknot recognizer, a general
subexponential recognizer, or any end-to-end timing gain.
