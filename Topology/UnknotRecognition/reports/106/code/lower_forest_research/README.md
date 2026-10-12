# Bounded lower spanning forest portfolio

This optional research producer is based on native revision
`c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`. It calls the ordinary
`normal_cut_handlebodies` first. Every native `COMPLETE` result is returned
immediately and unchanged. Following a native refusal, it retries the same
whole-cut producer with a private core-planner binding and these two policies:

1. Process one-handle edges whose raw columns have exactly three distinct unit
   owners before all other edges, keeping the original order within each group.
2. Process one-handle edges in reverse source order.

Each policy constructs a spanning forest, runs the existing geometric row-leaf
and column-leaf planners, and verifies any successful core proof with
`verify_core_handlebody_certificate`. The resulting whole-cut certificate uses
an existing native schema. It must be checked with the ordinary public
`verify_normal_cut_handlebodies` on the actual triangulation and coordinates.
No verifier accepts a prepared source from the adapter.

The first policy minimizes the number of remaining three-owner unit columns
in a raw source core: if these edges form `E3` in the original zero/one-handle
multigraph, the optimum is the graphic cycle nullity `|E3| - rank(E3)`.
Minimizing this parameter does not imply the best cancellation outcome. The
second policy supplies a deliberately different forest. This bounded portfolio
does not decide feasibility over all lower spanning forests.

## API

From the repository's `Topology/UnknotRecognition/fast` directory:

```python
from lower_forest_research import normal_cut_handlebodies_with_forests
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

result = normal_cut_handlebodies_with_forests(
    triangulation, coordinates,
    max_extra_forests=4,
    max_cycles=None,
    record_certificate=True,
    precheck_core=True,
    check=lambda: None,
)
if result['status'] == 'COMPLETE':
    assert verify_normal_cut_handlebodies(
        triangulation, coordinates, result['certificate'])
```

`max_extra_forests` bounds the total alternative forests across every core call
in the retry. Four permits both policies on an initial core and on a later
disk-bundle-augmented core. Zero disables the retry. The adapter stops at the
first successful core policy. It has no random search and retains no state
between calls. `max_cycles` is shared across the initial whole-cut call and
the retry. Callback exceptions propagate. Exhausted limits and unsuccessful
search return `INCONCLUSIVE`, which is not a negative topological result.

The adapter copies the imported composed function's globals using
`types.FunctionType`; it neither reloads a source file nor changes any public
module binding. Source charts and handle identifiers remain unchanged, and
only a local list of traversal references is reordered. This construction is
portable to the same native package version when installed outside a checkout.
It depends on the current composed producer's core-planner binding and does
not promise compatibility with future rewrites of that internal interface.

## Reproduction

The independent full native benchmark establishes 92 complete and 14 refused
cuts on the 106-case `marked_parallelity_research/corpus.json`. Its SHA-256 is
`97b4ceed6f068885760d80dea214538634998dd405b77e76926c1f93db03da5c`.
The following audit checks the corpus hash against that evidence, selects
*every* baseline refusal, recomputes the native status, tries the two policies,
and independently replays every newly successful whole-cut packet:

```sh
python -m lower_forest_research.audit \
  --baseline /path/paired_native_benchmark.json \
  --output /path/bounded_lower_forest_results
python -m unittest tests.test_lower_forest_portfolio
```

The October 12, 2026 audit found five additional independently verified
handlebody censuses. Its optional portfolio coverage is therefore **97/106**;
the maintained native default remains **92/106**. These are source-cut census
results, not a 97/106 standalone knot-recognition success rate.

| Source case | Successful alternative | Whole-cut genus histogram |
| --- | --- | --- |
| `pilot/fibonacci_lst_04/0` | exceptional first | genus 1: 1; genus 2: 1 |
| `pilot/fibonacci_lst_06/0` | exceptional first, raw and augmented | genus 1: 1; genus 2: 1 |
| `pilot/lst_4_9/0` | exceptional first, raw and augmented | genus 1: 1; genus 2: 1 |
| `pilot/finite_trefoil/0` | exceptional first | genus 2: 1 |
| `pachner23_5_8_2/mixed` | reverse | genus 0: 1; genus 1: 2 |

All five histograms also agree with the separately identified historical
Regina oracle report; that agreement is supporting evidence, not the new
proof. The proof evidence is each source-bound packet and independent native
replay. The five saved packet files exactly match those from the preliminary
broader exploration; the final adapter uses only the two deterministic
policies stated above.

The nine remaining refusals include two cases whose cores now cancel but
whose annular attachments remain unsupported (`fibonacci_lst_08` and
`fibonacci_lst_10`), one raw core that still stalls (`finite_figureEight`), and
six cases identified by the historical oracle as containing non-handlebody
components. The adapter continues to refuse all six. No negative certificate
or completeness claim is made for the nine refusals.

The focused tests cover successful independent replay and proof tampering,
exact preservation of baseline successes, unchanged source inputs and public
module bindings, operation without source-file loading, repeatability,
cancellation during forest traversal, invalid options, shared discovery-cycle
limits, global alternative-forest limits, and the need for the reverse policy.
