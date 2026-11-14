# Local research toward fewer than 208 working states

No accepted 207-state machine is supplied here. This is a bounded research
record. Two input graphs are representatives from the incoming History U208
packet pinned by the enclosing report; their bytes and hashes are in inputs/.
The history and compatibility graphs are not isomorphic. Other incoming
presentations are renamings, not independent reductions to stack.

## Completed families

1. Backward finite-history aliases and shared-branch folds use up to 12 old
   transitions of guard information and positive simulation segments of at
   most 60 transitions. The two input classes each admit 148 eligible
   noninitial state pairs and 122,544 fold actions. No new fold survives.
   An earlier depth 8/40-step pass is retained for provenance.
2. Exhaustive single-row actions with a 40-step exact one-transition macro
   contract yield 351 neutral rewrites in the history class and 357 in the
   compatibility class. They are equivalences, not state reductions. Shared
   representatives cannot be obtained merely by intersecting both rows'
   nonrecursive neutral alternatives in the history class.
3. A neutral helper rewrite can be combined with a shared-branch fold action.
   Each failed concrete fold trace identifies possible modified helper rows;
   only rows on that trace can fix that failure. The search tries the recorded
   neutral alternatives at those rows, then requires an exact composite proof
   at both merged controls and the modified helper. There are 3,138,357 and
   3,159,139 repair attempts respectively, with no accepted result. A helper
   that is not neutral on its own is outside this family.
4. Both rows of any merged noninitial pair may change, with no requirement of
   a shared literal row. Each class has 21,321 pairs. The guards intersect a
   nine-cell blank-run fixed point with depth 12 history information. Positive
   old and new blocks must join within 32 steps with identical head, control,
   and entire known window, without reading opaque exterior or reentering a
   merged control. Respectively 19,100,685 and 19,111,897 candidate actions were
   tested, with no accepted result. These sufficient templates are not a
   state lower bound.

The initial-control-inclusive variant also completed 207 pairs and 192,663
action trials in each class, with no result. The source-window-intersection
lane is bound only to the Entry primary class A table; it does not transfer
those guards to the nonisomorphic compatibility class. It completed 17,493 affected pairs (3,828 unchanged pairs covered by the
prior class A search were skipped), 15,388,630 action trials, with no survivor.
The raw receipt's `pairs=21321` is the final combination index, not the
number of affected pairs tested; `source_guard_stats.json` makes this
distinction explicit. Guard windows shrink from 26,731 to 20,547 across 119
states. The table and projection SHA-256 hashes are bound separately.

## Reproducibility and limits

`python3 -B verify_neutral.py` and `python3 -O -B verify_neutral.py` freshly
re-establish all 708 recorded neutral identities against the literal input
bytes. This uses the inherited finite-history and branching macro engine,
not an independent proof assistant. It recomputes 42,240 history-context
checks and 24,987 consistent symbolic branch obligations. Inconsistent
read/guard combinations are vacuous.

The larger synthesis passes are optional and may take several minutes. Copy
this whole directory to a scratch directory before running scripts that
write receipts. From that scratch directory, for example:

    python3 history_fold.py inputs/history.tm --depth 12 --limit 60 --output trial.json
    python3 window_two.py inputs/history.tm trial

The Python scripts
use only the standard library. To regenerate the neutral-helper lane run
`neutral.py inputs/history.tm` first, then `fold_neutral.py`; this writes a
large intermediate certificate JSON intentionally omitted from this compact
bundle. Compatibility uses the corresponding `_compat` scripts. The source
window lane additionally uses `inputs/entry_primary.tm` and
`inputs/source_windows.json`; `source_binding.json` records their exact
identity. The enclosing boundary projection bundle supplies provenance and
full projection replay. For example, run `window_source.py
inputs/entry_primary.tm source_trial inputs/source_windows.json` in scratch.

The backward-history guards hold on every run from state 0 with any initial
tape. The forward local-window fixed point is weaker in scope: it begins
with a blank initial window and overapproximates new exterior bits. Their
intersection therefore holds for every blank execution. A successful
candidate would still require all construction-specific proof obligations;
no negative search receipt asserts that all smaller machines are impossible.

Code provenance: `history_search.py` and `history_fold.py` are retained from
the incoming History208 research package. `window_base.py` and the original
nonrecursive join template derive from our preceding U209 local research.
The neutral-catalog, helper-composition and strengthened guard-intersection
lanes are this iteration's additions. No incoming table is altered.
