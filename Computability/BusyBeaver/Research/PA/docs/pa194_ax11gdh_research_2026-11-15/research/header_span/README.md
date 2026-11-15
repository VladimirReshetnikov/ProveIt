# Header-span and broader-entry bootstrap research

This is research on the inherited **193-state runtime core rejected for blank startup**.
It is not a new accepted blank-start consistency machine. The exact native table has
SHA-256 `50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.

## Provenance

The table and search-edit pool are copied from
`docs/incoming/pa194_lcfast_tagged_research_2026-11-14.zip` in the pinned ProveIt
snapshot `793c68737d94bffa4e32a75bce6cc8058d6d22f0`. The same core is filed at
`Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13/runtime193/`.
The source sites are the primary PA194 sites in
`docs/pa194_conpa_2026-11-13/construction/source/pa194.sites.json` under that PA path.

The independent engine and its control-label map are copied unchanged from the
LCFAST packet's `verification/independent/reference/`. The adaptive startup
search is adapted from its `research/startup_search/adaptive_startup.cpp`:
only the header-span constants are changed from 48 to 37, and a newly supplied
template file permits all 3,673 source-site paths. The inherited C++ source
SHA-256 was `f1af1b6675525cb056ede7ba0625bdff7a8e6d91528452347a5c3287fec84f61`.
All included inputs and sources are bound in `input_manifest.json`.

## Exact symbolic experiment

The primary source's maximum address length is 36. The older frame invariant
used header distance at least 48, leaving potentially unnecessary slack.
`check_header.py` selects a smaller distance and replays all source contracts
using the independent whole-tape symbolic induction engine. It rederives the
four list-traversal lemmas from the literal table, uses nine arbitrary natural
primary values, both decrement outcomes, an arbitrary nonempty spare list, and
an arbitrary nonnegative additional gap. No arithmetic-box oracle is used.

At span 37, the checker proved 4,223 outcomes and then stopped at source site
3248, zero branch. A literal step required a zero-run atom whose length could
be zero. This is an **inconclusive symbolic failure**, not a counterexample
and not a proof that span 37 is impossible. The exact error is retained in
`header_37.json`. At span 38 all 4,780 outcomes passed: 1,078,534 symbolic events, minimum
positive duration constant 3, and all 386 literal rows used. This establishes
the unchanged runtime contracts with a header distance ten cells smaller
than the inherited 48. The exact receipt is `header_38.json`. It does not
claim that 38 is minimal or provide a blank initialization.

Run with Python 3 and assertions enabled:

```sh
python3 check_header.py 38
```

The historical span-37 run can be reproduced with argument `37`; it intentionally
exits nonzero when the symbolic proof stops. These are local runtime theorems,
not startup or arithmetic-calibration theorems.

## Bounded adaptive startup search

The exploratory search used span at least 37 and every primary source-site path.
It allowed arbitrary values of all nine primary registers and a nonempty spare
list, with complete zero tape exteriors. It retained the inherited prefilter
requiring at least 13 one-cells. A theoretical frame with an all-zero path, nine
zero primary values and one zero spare has only 12 one-cells and is outside
that recognition criterion. This limitation matters when broadening beyond the
old sites 25--44; the experiment is not described as exhaustive over all frames.

The command requested 16 edit depths, beam width 256, a 50,000-step per-run
limit, all 193 initial controls, seed 1137193 and a 90-second wall budget.
It completed six depths and part of the next before the wall cutoff:

| Measured quantity | Result |
|---|---:|
| Distinct start/edit configurations simulated | 28,438 |
| Literal transitions | 989,809,484 |
| Complete-frame hits | 0 |
| Literal halts | 5 |
| Recognized outward blank rays | 8,643 |
| Resource-bound stops | 19,790 |
| Visits to control 84 | 611,157 |

The 28,438 configurations include the unedited 193-start baseline. They are
distinct start/edit specifications, not necessarily distinct reachable
transition systems: an edit can become inactive. The search's row pool was
screened individually in restricted runtime contexts by its source packet.
Simultaneous preservation of arbitrary edit combinations is not assumed.
Any hit would still require a fresh whole-runtime proof and a valid semantic
source seed. No hit was found, so no edited table is promoted.

The exact discovery command was compiled with `-O0`:

```sh
g++ -std=c++17 -O0 adaptive_header37.cpp -o header37-search
./header37-search inputs/runtime193.native.tm inputs/neutral.tsv \
  all_source_templates.tsv 16 256 50000 90 -1 1137193 \
  > header37_startup_hits.jsonl 2> header37_startup.log
```

The wall-clock cutoff makes the final partial depth hardware dependent. The
delivered log and empty hit stream preserve the actual run. A resource-bound
stop gives no conclusion about later execution. Neither this experiment nor
the failed symbolic span-37 proof is a state-count lower bound.

