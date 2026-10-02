# Waterfall report review and complete boundary reduction

The Waterfall report's mathematical claims pass review: its fixed 46-clock
matrix simulates the supplied universal machine on arbitrary natural half
tapes, and its quadratic exactly describes first halting at an externally
fixed source-machine horizon. All eight original replay commands pass.
Two Python interface defects have a checked repair. The complete seven-step
polynomial now has **107 natural witnesses and a 720-operation evaluation**,
down from 245 witnesses and 1558 operations in the same evaluator.

These are finite-horizon certificates. The established universal polynomial
bound remains **87=48M+39A**, and the separate 75-operation comparison
certificate is unchanged. The growing horizon and ordinary-program input
encoding must still be paid before any universal comparison is possible.

## Frozen material and reproducibility

The reviewed archive is `docs/incoming/Waterfall_Diophantine_Certificates.zip`,
delivered at `24a743255`, with SHA-256
`b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`.
The archive and all 31 supplied members remain unchanged. The earlier
[triage](waterfall_intake_triage_24a743255.md) records the initial read scope;
this packet completes that review.

The [one-command replay](waterfall_report_review_24a743255.py) checks the
archive against both the working intake and its arrival commit, safely
extracts private copies, executes all eight original commands, checks every
original member byte, and reruns the pinned independent helpers. Its
[receipt](waterfall_report_review_24a743255.json) retains the complete member
inventory, helper hashes, command results and independent results. The
arrival-commit fallback also works after an intake retires the archive.

From this directory, run:

```sh
python waterfall_report_review_24a743255.py
```

Use `--write` only to regenerate the saved review receipt. Python's standard
library, Git and the `patch` command suffice; assertions must be enabled.
No LaTeX rebuild or visual audit of the report's own PDF is claimed. The
primary paper's machine table and halting configuration were checked visually.

## Findings

| Area | Finding | Evidence |
|---|---|---|
| Fixed substrate and input | PASS: 46 physical clocks; the extra serialization row/column is metadata | [Frontend proof review](waterfall_frontend_review.md) |
| Universal-machine source | PASS: all 30 table cells, initial A0 convention and missing J1 halt agree | Primary sources and exact source hashes in the frontend review |
| Unbounded macrostep loops | PASS: strict minima at every event prefix, including zero-repeat boundaries | 58 exact macrosteps, 43,065 endpoint inequalities, 2,668 final-coordinate identities |
| First-halt quadratic | PASS over natural coordinates; its witness fibre is empty or singleton | [Polynomial review](waterfall_polynomial_review.md) |
| Python input/export contracts | Two defects reproduced and repaired | [Exact-domain patch](waterfall_grouped_exact_domains.patch), unchanged valid exports |
| Complete projected compiler | PASS: affine restoration, natural-zero bijection and full arithmetic schedule | [Reduction proof](waterfall_forced_boundary_projection.md), [independent review](waterfall_forced_boundary_review.md) |
| Common-column theorem | PASS in its positive-relative-diagonal class; its 22/26-operation examples are decidable | Frontend review and independent stream/CRT checks |
| Endpoint-only unbounded shortcut | Rejected on the actual universal matrix | [Exact integer counterexample](waterfall_endpoint_alias.md) |

The [Neary–Woods primary paper](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf)
proves the 15-state binary machine universal through bi-tag simulation. Its
Table 16 and displayed halting configuration agree with the report; nearby
prose uses the wrong symbol. The report identifies that discrepancy correctly.
The [author-deposited metadata](https://mural.maynoothuniversity.ie/id/eprint/12416/)
also explains the deposited PDF's incorrect pagination. This review does not
claim that the paper's historical machine-size record remains current.

The upstream [machine](https://raw.githubusercontent.com/Iijil1/MTGPrograms/main/Examples/UniversalTM15x2.tm.txt)
and [matrix](https://raw.githubusercontent.com/Iijil1/MTGPrograms/main/Examples/UniversalTM15x2.twm.txt)
were independently downloaded and match the delivered bytes. The fixed
matrix's all-input simulation is established directly; no execution or new
audit of the upstream compiler is needed. The four-operation raw half-tape
loader is correct, but does not include translating ordinary programs into
those half tapes.

## Complete polynomial improvement

The first instruction is forced to be A0. The three instructions before
halt are forced to be G0, H0 and I1. Fix their selectors and inactive tape
groups, then restore their remaining determined coordinates by nonnegative
affine expressions. Two internal suffix quotients become `2QI+1` and
`4QI+3`; the entering left tape is `8QI+6`, and the final right tape is
`8Y+3`. Every erased coordinate is natural for every retained natural
assignment, including false witnesses.

For `k>=4`, this removes 138 witnesses, 19 affine squares and eight
nonnegative products. The complete resulting polynomial has `35k-138`
witnesses, `5k-15` squares and `2k-8` products, with exact degree two. The
shortest disjoint case `k=4` retains the nonzero state residual 5, so it
correctly has no zero. Prefix-only mode covers smaller positive horizons.

| Seven-step complete form | Witnesses | Squares/products | M | A | Total |
|---|---:|---:|---:|---:|---:|
| Parent | 245 | 39/14 | 430 | 1128 | 1558 |
| Forced prefix | 211 | 34/12 | 373 | 984 | 1357 |
| Forced prefix and suffix | 107 | 20/6 | 203 | 517 | 720 |

The 838-operation saving is an achieved literal schedule for the whole
relation at `k=7`, with arbitrary supplied `L0,R0,C,tau`. It is not just an
evaluation at the displayed halt. Constants/copies are free; binary
addition, subtraction and multiplication, including scalar multiplication,
are charged. All emitted gates reach the output. No division, variable
power, linear-form oracle or claimed arithmetic lower bound is used.

The independent checker expands every gate and every parent substitution
as an integer sparse polynomial for 21 mode/horizon combinations. The
results agree coefficient-for-coefficient. It also checks all operation
counts, restoration forms and public canonical-packet guards. The structural
proof establishes the all-horizon natural-zero bijection; the finite
coefficient checks independently verify the emitted implementation.

## API repair and verification limits

The original grouped compiler accepts floating-point natural inputs and
Boolean witnesses, even at the seven-step zero. Its exported parameter and
witness name lists also alias live compiler metadata. These are interface
defects, not counterexamples to the natural polynomial theorem.

The separate patch validates exact integer formal coefficients and values,
exact natural certificate coordinates, complete coordinate sets, positive
horizons and early-halting lifts, and detaches exported name lists. Signed
formal polynomial evaluation remains available explicitly. The patch does
not claim to protect arbitrarily modified compiler internals or Python
methods. It is applied only to disposable copies, preserving the original
archive as evidence.

Five relevant author commands pass on both original and repaired copies,
with all 12 shipped JSON outputs byte-identical. The repair checker rejects
1,816 malformed calls and verifies owned export/term containers. The separate
projected compiler rejects 9,898 malformed calls in the independent audit,
and its archive/source authentication is also checked under optimized Python.
Exact symbolic proofs establish the mathematical result; these finite API
and simulation checks exercise the implementation, not every possible input.

## Unbounded-history obstruction and next direction

For the actual 46-clock matrix, a fixed nonnegative nonhalt firing-count
vector satisfies `Mv=194*1`, with 62 firings and ten control events. Adding
it to the real seven-instruction halt preserves the full canonical endpoint
and exact time equation but changes `(C,k,tau)` from `(189,7,428)` to
`(251,17,622)`. A direct strict-minimum event replay proves that the same
input already halted at 428. More generally, adding any positive multiple
gives another false endpoint witness.

This rejects the explicitly stated count/endpoint/time bundle; it does not
reject the report's full ordered-history quadratic or every possible
nonlinear history representation. Any next fixed-dimensional compression
must account for event order and reject this concrete family.

The useful next experiment is a fully costed packed recurrence on the two
binary tape halves, including selected fields, rule lookup, shared length,
input conversion and finalization. Returning to literal Waterfall events
would reintroduce repetitions that the proved macrosteps already remove.
Component identities and conditional interface counts remain research leads
until those obligations are discharged. The separate
[unbounded-history scout](waterfall_unbounded_scout.md) preserves the
15-candidate scheduler quotient, explicit conditional 27-operation tape
interface, and a separately replayed [source-pinned algebra checker](waterfall_unbounded_scout_checks.py).
That scout's finite checks are additional to the main review command;
they do not certify the unpaid packed-field conditions.
