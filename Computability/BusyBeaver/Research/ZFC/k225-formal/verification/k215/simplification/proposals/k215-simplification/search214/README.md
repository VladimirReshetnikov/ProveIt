# Proof-directed local folds below 215 states

**Result: no 214-state survivor in the bounded family described below.**
This is an executable research supplement, not a state-count lower bound or
a newly certified consistency machine.

The inputs are six exact native tables at ProveIt commit
`b6c7087477e51c017003bd729e712c8969733223`: primary K215, conditional-marker
CM215, direct-transfer ST215, zero-spare-transfer, MP-first-transfer, and
rebalanced K215-R41. `input_pins.json` gives exact paths, SHA-256 digests,
byte lengths and Git blob identities. All inherited machine/calculus/compiler
authorship is retained; see `licenses/` and the pinned source paths.

## What the search covers

- All 23,005 unordered state pairs in each input; the declared initial state
  is retained when it belongs to the pair.
- Both rows of the retained state may change; all other rows retain their
  actions with removed-state targets redirected.
- A fixed-point nine-cell window invariant overapproximates every run on
  every initial binary tape. Newly exposed boundary bits are nondeterministic.
- Every write bit, direction and remaining working/halt target is considered.
- Each local block uses at most 48 steps, stays within the represented window,
  and has no internal revisit to either merged state before its endpoint.
- Every old step at the two merged states must have a positive matching new
  block, including exact state, head and entire-tape effects.
- Identical local contexts may match different old targets at different
  positive durations; no overlap screen excludes these possibilities.

This family found no survivor on any of the six inputs. It does not exclude
wider invariants, longer blocks, joint edits, reentrant helpers, new source
programs, or new formalisms. A control recovers the known 69/400 fold from an
explicit unfolding; early halt and wrong selector controls fail as expected.
The abstract invariant's closure is independently checked using tuple shifts.
A separate control checks a common trajectory matching distinct old targets
in one and three steps respectively.

`reduction_section.tex` gives the invariant proof, transfer theorem, search
scope, table of results, and a concrete next extension. These are ordinary
mathematical proofs and executable finite checks, not newly kernel-compiled
Lean/Rocq results. The separate CM215 transfer development in the containing
report has its own proof-assistant status.

## Reproduction

Python 3.10+ and its standard library are sufficient, with assertions enabled.

```sh
python3 reproduce.py
python3 reproduce.py --search
```

The first checks all input identities, table well-formedness, invariant
closure, positive and negative controls, and stored receipt identities,
including SHA-256 bindings to the exact search and abstraction scripts. The
second freshly replays all six bounded searches and compares stable receipt
fields. Temporary outputs go outside this packet. Existing receipts are not
overwritten by the reproduction driver. The driver rejects Python's `-O`
mode because the finite audit uses assertions.

The standalone research tools are in `tools/`. Only `indexed_fold_search.py`
is needed for the full search; `window_fold_search.py` also contains the direct
local simulator used by the independent controls. `evidence/` contains the
actual fresh run receipts. No archive in this supplement is required.

New search scripts and exposition may be incorporated into ProveIt under the
repository's existing license. Original tables and inherited contributions
retain their original terms and attribution.
