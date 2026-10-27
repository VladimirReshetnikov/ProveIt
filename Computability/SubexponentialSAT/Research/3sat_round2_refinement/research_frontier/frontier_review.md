# Algorithmic frontier review — stronger order not established

## Status and scope

The requested success criterion is a genuinely smaller unrestricted exponent
than `n loglog(n)/sqrt(log n)`, not formalization catch-up, a smaller numerical
coefficient, or a density promise. I found no proved algorithm meeting that
criterion after direct review of the precision, factorial-Cauchy, parity-lift,
and density-refinement source reports. Their stronger order statements remain
explicitly conditional. All complexity assertions below inherit the correctness
of the unchanged OpenAI manuscript; no entire source theorem was reverified.

No upstream program was executed. The local exact-arithmetic checker was written
independently for this review and checks algebraic finite cases only.

## Exact source anchors

Paths below are relative to `sources/proveit/extracted/`:

* `3sat_precision_refinement_2026-10-26/3sat_precision_refinement/report.tex`:
  sections `sec:precision`, `sec:compressed`, and `sec:conditional`;
  equations `eq:new-precision`, `eq:rank-budget`; hypothesis `hyp:acceleration`.
  The precision decrement 24 to 6 is proved conditional on the source algorithm,
  but preserves the square-root logarithmic order. The exact beta-rank network
  has `O(M/sqrt(u)+r^2)` wires, but its genuine group tensors have excessive degree.
  `hyp:acceleration` is the missing structured summation theorem, not an algorithm.
* `cauchy_mode_improvement_2026-10-26/cauchy_mode_improvement/report.tex`:
  lemmas `lem:actual-domain`, `lem:entropy`; theorem `thm:weights`;
  equations `eq:newweights`, `eq:det-valuation`; section `sec:limits`.
  Integral source/target separation is compatible with the extension ring because
  actual rows satisfy a prime-subring congruence, not because every extension-ring
  element has integral binomial coefficients. Weights `3b+1-2 popcount(b)` remain
  linear, giving the constant `1/sqrt(3)` entropy comparison, not a new order.
* `3sat_refinement_package/3sat_refinement/3sat_refinement_report.tex`:
  section `sec:conditional`; assumption `ass:LF`; lemma `lem:extension`;
  theorem `thm:conditional`. The missing `LF` must factor every generated group
  tensor, including invalid-rank zeros, into `O(W)` total Boolean edges and maximum
  degree `W^0.9`, with construction and entry cost
  `poly(s) exp(O(s/log(s)+s^0.9))`. Keeping its original child network costs Theta(M)
  edges and does not meet the assumption. The precision extension is an explicit
  technical repair, not a proof of `LF`.
* `eth_density_refinement/eth_density_refinement/report.tex`: sections
  `sec:limits`, `subsec:smith`, `sec:research`; equation `eq:smith`.
  Already contains the exact odd-Cauchy Smith valuations `4b-2 popcount(b)`.
  Do not attribute that profile to this second-round review.
* Prior source `eth_3sat_improvement_20261027/source/build/quantitative-contraction.tex`:
  labels `eq:tensor-deformed-contraction`, `eq:tensor-precision-bound`,
  `eq:tensor-mode-budget`, `eq:tensor-recursion-identity`.
  The degree is tied to Boolean port wires, not pre-encoding incidence degree.
* Prior source `.../quantitative-reduction.tex`, subsection
  `subsec:tensor-interface`: the interface permits bipartite **multigraphs**.
  Parallel-edge collisions cannot silently be removed from packing estimates.

## Current distinct algorithmic gates

1. **Degree-sensitive compressed deformation.** A root incidence polynomial of
   degree `K=O(n)` does not yield binary encoded degree `O(n)`. Both the degree and
   the `O(compressed_wires/D)` mode multiplicity must survive every child. An
   exterior-power identity supplies a local degree bound but ordinarily counts
   modes by the uncompressed incidence universe. This is the missing constructive
   and recursive lemma in the prior degree-kernel conditional result.
2. **Structured mode aggregation.** The beta-rank graph is an exact representation,
   but its high-arity group tensors do not inherit the published degree bound.
   Equality-tree splitting is invalid for arbitrary group tensors; returning to
   their original child networks loses compression. A bounded-degree factorization
   with total edge, entry-oracle, creation-precision and construction costs is needed.
3. **Different operator algebra.** The separate `eth.pdf` manuscript suggests an
   effective graded operator family with entropy `exp(O(E^alpha))`, `alpha<1/2`.
   The unchanged Heisenberg/Fock algebra cannot supply one: the exact creation and
   annihilation relations make all partition-indexed vacuum states independent.
   See sibling agent note `research_alternate/heisenberg_entropy_barrier.md` for the
   proof, nonlinear-regrading failure and sparse-current locality obstruction.

These gates are alternatives, not established ingredients that can be combined
into an unconditional improved theorem. Multiplying numerical improvements from
precision, factorial modes and packing leaves the same square-root order.

## Actual-domain clarification and checks

`actual_domain_rank_gate.tex` embeds the density report's odd-Cauchy block in
actual packet slots and proves the exact modular approximation-rank corollary.
This closes the temptation to evade linear mode weights merely by arguing that
the auxiliary rows are not actual rows. Conversely, the note explicitly warns
against claiming a slope-three optimum on actual rows: congruence exclusions
prevent the easy auxiliary-domain transfer.

`check_actual_cauchy.py` is a new independent standard-library verifier;
`actual_cauchy_checks.json` records 3,804 exact minor checks across 18 matrices
of sizes 1 through 6, plus actual reciprocal-row residue checks. The generic odd
shift 3 is a control; shifts 17 and 65 occur in the actual-node specialization.
These checks do not establish the asymptotics or execute the full SAT algorithm.

## Costs and space that cannot be omitted

Any improvement must retain deterministic exact arithmetic, polynomial-size
coordinate precisions, polynomial-size immutable tensor descriptions, and a
fixed polynomial dependence on the input description length. Each generated
entry must retain its creation-time representative when later precision rises.
An oracle that merely evaluates a high-arity group tensor in subexponential time
is not a bounded-degree tensor factorization. Neither exponentially many live
entries nor a larger coefficient ring can be hidden in a claimed polynomial-space
bound. Directly lowering the leaf threshold does not lower the root mode entropy.

## Conclusion

There is no identified denied permission or acquisition blocker on this track.
The blocker is mathematical: none of the reviewed sources or my independent
attempts constructs any of the three missing interfaces above. The useful outcome
is a sharper separation between genuine new order-level targets and proved local
constant refinements, plus an actual-domain guard against overclaiming a local
kernel speedup. No stronger unconditional 3SAT order is asserted.
