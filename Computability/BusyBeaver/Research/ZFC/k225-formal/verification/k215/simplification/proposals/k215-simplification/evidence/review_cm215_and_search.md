# Independent review of the root report and state-search scope

## Resolution at release, 2026-10-21

The overlap-screen finding below is resolved. The screen was removed, an
explicit one-step/three-step shared-context regression control was added,
and all six searches were rerun at radius 4 with a 48-step bound. Each
corrected receipt has `overlap_screen: false`, 23,005 pairs, and no survivor.
The final rerun also binds the exact search and abstraction script hashes.
The reproduction driver checked those receipts and the independent controls.
The corrected total is 138,030 pairs; this remains a bounded-family negative
result, not a lower bound. The natural-number wording below was also fixed.
The original review follows as a record of the finding and its rationale.

Reviewer lane: simpler_candidate. Review is read-only with respect to the
report and search implementations. Snapshot reviewed: root report.tex and
search-results.tex on 2026-10-21, with results.tex still being finalized.

## CM215 exposition: PASS

I checked the six native row edits, the state map, all three invariant clauses,
the invariant-preservation argument, the one/three-step blocks, the arbitrary
whole-tape/head quantification at initial state 0, and the generic stuttering
argument against the compiled Lean files. These statements are accurate.
The exact schedule t+2z(t) follows from the shown local cases. The distinction
between an existing machine and a new relative formal proof is correct. The
AdapterStatus text correctly states 363 new proof lines, 462 generated data
lines, 27.543 seconds for the clean six-module check, and exclusion of the
preexisting KDense215 dependency build from that timing.

The parameterized inherited calibration theorem does not by itself constitute
a new fresh full ZFC-closure build; the report appropriately keeps that status
separate. Its explanation of totalizing the halt does not inflate the physical
state count or introduce stay-put working transitions.

Minor wording recommendation: in Positive-stuttering transfer, write "natural
number k>=1" instead of "integer k>=1" to match the formal iteration type.
Positive integers are mathematically equivalent here, so this is precision,
not a mathematical defect.

## Search review: required restriction identified and being corrected

The initially reviewed indexed_fold_search.py rejected a pair before checking
blocks whenever the two old states admitted the same local window but their
projected one-step effects differed. That rejection is not necessary for a
positive-stuttering simulation: one deterministic target trajectory may reach
two different required endpoints at different positive times, depending on
which old logical state is represented. Thus this screen could cause false
negatives. It did not cause unsound accepted candidates, and no survivor was
claimed.

I reported this to state_reduction and root. State_reduction agreed, removed
the overlap-effect screen, and is rerunning all six indexed searches. Final
counts/receipts must come from those corrected runs. Until that is complete,
claims must either state the extra restriction explicitly or remain limited
to the older bounded family. The root's general no-214/no-lower-bound wording
is already appropriately cautious.

## Remaining indexed-search mechanism: consistent with stated scope

The sliding-window closure starts with every local bit pattern at state 0 and
nondeterministically inserts each newly exposed boundary bit. It therefore
overapproximates arbitrary-tape reachable contexts. For each admitted local
context, indexed blocks include the proposed first row and then literal
unchanged helper rows. They cannot read outside the represented window, and
they must reproduce the required write, head displacement, and projected
successor. Noncentral cells of the entire inspected window are restored;
untouched exterior cells are unchanged. The search excludes an internal visit
to either merged state, so changes to the retained rows cannot invalidate an
accepted helper trace. Reaching a merged control at the final boundary is
handled by the projection. Positive durations are counted from one.

The first occurrence of a fixed local endpoint dominates a later occurrence
because the accumulated set of internal helper controls is monotone; retaining
only the first occurrence for each action/endpoint does not remove an otherwise
admissible block in this class. Unordered pairs with one chosen survivor label
are adequate up to renaming of the surviving control, while preserving start 0.
The provider pool includes the designated halt as well as surviving working
states, as reflected in the code's action counts.

These checks support only the specified finite-window, bounded-length,
unchanged-helper class, with a whole-tape-equality boundary relation and no
internal visits to folded states. They do not establish actual reachable-window
precision, completeness over arbitrary stuttering transformations, or a
state-count lower bound.

## One-row search

window_fold_search.py is narrower: the pair must have a literally identical
common-symbol row, only the other retained row is replaced, and the surviving
table's other targets are projected. candidate_check then executes the actual
proposed folded rows, including any allowed revisits, within its finite window
and step bound. This scope is stated in its result string. The reachability
abstraction is the same sound overapproximation. An empty set of contexts for
a branch can pass vacuously because that branch is unreachable under the
abstraction; ordinary reachable steps still have positive simulation length.

No further mathematical error was identified in the inspected mechanisms.
The corrected indexed results need final consistency checking against their
updated code hashes and README before packaging.
