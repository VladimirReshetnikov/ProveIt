# Nine substrate reports: completed mathematical and executable reviews

The nine archives delivered at `060e08a07` and `2a8a39599` have now received
complete report/source reviews and original author replays. No counterexample
was found to their mathematical theorems under the stated hypotheses. Several
executable certificate checkers and input interfaces required the separately
recorded repairs below. The incoming archives remain unchanged.

The [intake record](incoming_substrate_intake_2a8a39599.md) is a historical
inventory of 231 files and 54 Python modules, not a proof review. The completed
reviews linked here supersede its pending status. They distinguish natural
integer witnesses, polynomial or field witnesses, fixed-base powers, infinite
clock functions, and externally bounded families. None supplies a new
fixed-arity universal operation bound below 87.

## Results by archive

| Report | Reviewed result and implementation findings | Cost still outside a fixed universal polynomial |
|---|---|---|
| [Linear Boundary Transport](review_boundary_sandpile_060e08a07.md) | Exact finite-support linear certificate with `q+d` rows and `q+2d` polynomial witnesses; strict Boolean clock-mode repair | Polynomial coefficients/support are not a fixed ordinary integer tuple |
| [No Borrowed Firings](review_boundary_sandpile_060e08a07.md) | Natural quartic sandpile certificates and an exact source projection removing three witnesses and rows per vertex | Finite graph size is external; field witnesses still need fixed-arity scalar encoding |
| [Positive Spectrum](review_spectral_060e08a07.md) | Canonical positive-spectrum sign profiles; authenticate every difference-chain step and freeze coefficient data | Fixed-base power atoms need an ordinary Diophantine graph; uniqueness/finite-fold costs remain open |
| [Spectral Guards Without Time Expansion](review_spectral_060e08a07.md) | Fixed-shape power-assisted guards and ordinary bounded quartics; replace two-point expansion sampling by full coefficient equality and enforce exact scalar/index contracts | The ordinary quartic has an external bit width and changes arity with it |
| [Clock Spectra](review_spectral_060e08a07.md) | Exact finite counter-history packets and infinite clock-degree constructions; immutable machine snapshots and exact binary input repair | The infinite statement quantifies a clock function and infinitely many finite witnesses |
| [Unique Polynomial Histories](review_unique_polynomial_histories.md) | Full coefficientwise polynomial-history proof, including a nine-row feature system; reject noninteger symbol aliases creating undeclared witness names | Witnesses lie in `N[X,Y]`; an ordinary scalar expansion depends on external degree bounds |
| [Conservative Signal Frontend](review_conservative_signal_2a8a39599.md) | Literal 18-live-signal simulation, 49,700-mode/80,501-branch closure, quadratic step packet and exact compact ledger; repair dimensions, types, slack counts and nested snapshots | Prepared rational input, large finite mode code, and external history horizon are still charged |
| [Universal Membrane](review_membrane_reports_2a8a.md) | Literal direct/prime universal frontends and deterministic quadratic natural certificates; no supported-input defect found | Ordinary loading and unbounded time are not supplied by the finite-horizon packet |
| [Membrane Motifs](review_membrane_reports_2a8a.md) | Exact old-resource allocation, inclusion maximality, bottom-up updates, division/dissolution and indexed quartic schemas; no supported-input defect found | Finite catalogue and decorated schedule remain external; only the derived coordinates have the stated uniqueness |

These are mathematical and executable reviews, not proof-assistant
formalizations or certifications of historical priority. The detailed notes
state which primary sources were checked and any access limitations.

## Concrete reductions and useful transfers

**Sandpile source projection.** In the new quartic report, write the retained
slacks as `alpha,beta`. Substituting
`u=z+alpha`, `k=e+beta`, and `r=z+e+beta` removes three coordinates per vertex.
The deleted rows follow from the retained inactive rows; this gives an inverse
restoration on complete natural zeros. The source ledger changes from
`11n+12m` witnesses and `12n+16m` quadratic rows to **`8n+12m` witnesses and
`9n+16m` rows**, where `m` counts unordered adjacent pairs independently of edge
multiplicity. On the three-dimensional lattice it changes **47 to 44 fields
and 60 to 57 local rows**. The SOS polynomials need not agree away from their
zeros. The replay checks the actual source substitutions and complete SOS
correction, not just the count formula. No straight-line operation count or
fixed-arity scalar compression is claimed.

**Bounded direct membrane prefix.** The initial scratch test is forced to take
its zero branch. Substituting its selector and bases removes **2,811 witnesses,
five affine squares and 761 nonnegative products** at every external horizon
`T>=1`. The resulting counts are `2811(T-1)`, `5(T-1)+1`, and `761(T-1)`.
The terminal row remains. This is a proved bounded-family affine projection in
the review note; it is not a newly shipped general compiler or arithmetic
operation record.

**Inactive branch penalties.** The membrane quadratic uses
`(sum of other selectors)*(own selector + retained bases)` to force a unique
active branch even on the nonnegative real orthant, with natural initial data
then forcing natural execution data. The signal packet uses the related
homogeneous-copy construction. These are useful finite compilation techniques;
their respective external horizons still have to be represented at fixed cost.

**Cubic obstruction.** The separately reviewed
[canonical report Part XVI integration](review_canonical_revision_cb8238b64.md)
preserves the older cubic sandpile construction. Its joint nonnegative-real
cubic format has effectively semilinear natural zero projections, precluding
a universal fixed-arity compression that preserves that format. This is a
different report from the new quartic No Borrowed Firings archive and uses an
ordered-adjacency ledger. The obstruction does not extend to arbitrary
sign-changing cubics or quartics. The integration preserves 50 source/export
files byte-for-byte; the stale organization table is corrected and the PDF
rebuilt to 452 pages.

## Replay and repair evidence

Run these maintained commands from the repository root, with the pinned
research dependencies installed:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_boundary_sandpile_060e08a07.py
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_spectral_060e08a07.py
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_unique_polynomial_histories.py
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_conservative_signal_2a8a39599.py
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_membrane_2a8a39599.py
```

Each complete review has a saved receipt and authenticated inputs; portable
replays extract private copies and preserve the original incoming bytes.
Retired archives can be recovered from the pinned arrival Git objects. The
repair patches are applied only to review copies and leave correctly shaped
valid formula exports unchanged. All original author entry points pass, as do
the affected repaired entry points. Mathematical outputs are compared exactly;
only explicitly documented timing/platform metadata is excluded where present.
The trillion-term conservative-signal expansion is counted and audited through
its compact representation, not emitted.

The most consequential checker findings were a forged exponential difference
chain accepted as a sign proof, a forged quartic accepted by two sampled
evaluations, and a padded endpoint accepted by the generic signal evaluator.
The repairs validate the complete relevant mathematical object. Smaller exact
scalar, indexing, Boolean-mode and mutable-input defects are documented beside
their reproductions. Passing the original finite suites alone would not have
excluded these defects.

## Current research frontier

The independent [centered U15 compiler](u15_packed_centered_states611.md)
now evaluates its complete direct ordinary-input tape construction in
**611=239M+372A operations**, or 368 at the raw half-tape interface. It retains
102 positive witnesses, 46 comparisons and exact degree 1936. The source and
full polynomial identities received an [independent review](review_u15_centered611.md).
This is an improvement to that direct tape route; the overall universal
**87-operation** polynomial and separate **75-operation** certificate remain
the comparison bounds.

The next useful transfers should pay the ordinary input, acceptance and
unbounded-duration interfaces, or produce a complete source-level arithmetic
ledger for one of the proved finite projections. A smaller local degree,
fewer field variables, or a compact infinite semantic description alone does
not establish that universal arithmetic improvement.
