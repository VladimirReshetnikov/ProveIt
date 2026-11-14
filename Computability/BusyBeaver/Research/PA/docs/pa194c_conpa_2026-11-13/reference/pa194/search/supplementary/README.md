# Supplementary exploratory evidence

This directory preserves the small receipts, context data and exploratory
scripts supporting the report's additional negative-search observations.
These experiments concern the supplied **195S** tree, its raw 201-state
decoder, and the intermediate **195X** cross tree. They do not define or
verify the final 194-state construction. The primary portable verifier is
`../../construction/build194.py`.

## Recorded observations

| Experiment | Recorded scope | Outcome | Receipt |
|---|---|---|---|
| Longer two-cell fold detours, retaining the six supplied folds | 19 zero-context readers times 28 one-context readers; 80-step search budget | No additional compatible fold | `receipts/extended_folds_receipt.json` |
| Longer entry prefixes, retaining the six supplied folds | Prefix lengths 2, 3 and 4; respectively 871, 1,097 and 1,240 disjoint-context pairs | No additional compatible fold | `receipts/prefix_folds_k2_receipt.json`, `prefix_folds_k3_receipt.json`, `prefix_folds_k4_receipt.json` |
| Raw decoder with four-bit entry prefixes | 1,798 disjoint-context pairs, before applying any folds | Eight action variants on six distinct pairs; these are the six existing fold pairs | `receipts/raw_prefix_folds_k4_receipt.json` |
| Source-frame context extraction | All 4,780 symbolic source contracts plus the 58,154-transition blank startup | 9,760 distinct symbolic frame observations; 8,758 radius-four patterns for 172 non-box controls | `receipts/symbolic_contexts_receipt.json` |
| All-state local first-action search using those stronger contexts | Radius four, 80-step bound; arithmetic-box controls excluded as merged controls | No pair emitted | `data/symbolic_merge_choices.jsonl` and `logs/symbolic_merge_progress.log` |
| Reordering seven unconditional emitted heads | All 7! = 5,040 orders on each of the fixed 195S and 195X leaf-tree shapes | Best optimistic matching bound 195 on each shape; no candidate below 195 | `receipts/head_permutation_results.json` |

The empty `symbolic_merge_choices.jsonl` is intentional: it preserves the
search's empty standard output. The companion progress log shows the
per-control first-action scan. The context file is
`data/symbolic_patterns_k4.txt`; each line is `state bitmask`, with bit zero
at offset minus four and the current cell at bit four.

The annotated head-permutation receipt adds the experiment's scope and
pruning explanation without changing its recorded counts. For raw reader
count `n > 120`, even `floor(n/2)` disjoint pair folds leave
`134 + ceil(n/2) >= 195` states. Such cases cannot yield a strict improvement
within that specific pair-fold model. The score on the other cases uses
optimistic maximum matching; it is not a full simultaneous-fold or physical
correctness certificate.

These are bounded or template-specific negative results. They do not
establish a general lower bound. In particular, changing the decoder tree's
association subsequently produced the verified 194-state result.

## Historical originals and path-adapted copies

`originals/` preserves the scripts **byte for byte as run during the
investigation**. These files are historical provenance, not standalone
portable verification programs. The four original root-search scripts refer
to the temporary location
`/dev/shm/pa_reader_search/pa_consistency_research/construction195`, import
its `support` module, and write into a working-directory-relative
`root_research/` directory. The original head-permutation script refers to
the earlier `pa195_new_designs` setup. Those historical paths are not part
of this release.

`portable/` contains path-adapted copies using the release's unchanged
compiler and the frozen parent inputs:

- `../../construction/inputs/parent195S.grammar.json`
- `../../construction/inputs/parent195S.folds.json`
- `inputs/cross195X.grammar.json` for the second head-order experiment.

The adapted copies write to a new `generated/` directory beside this README,
so they preserve the recorded receipts. Their search algorithms are
unchanged; the modifications select packaged input paths and new output
paths. `portable/support.py` contains the unchanged `apply` and
`localvalid` helper functions extracted from the supplied PA195 support
module. Original licenses and source-archive provenance are in the primary
construction directory.

These path-adapted scripts were parsed for Python syntax during packaging;
the supplementary searches were **not rerun** at that stage. The recorded
receipts are from the original executions, and their original timings
should not be attributed to the adapted copies. `manifest.json` lists
origins, sizes and SHA-256 hashes.

## Optional replay commands

From this directory, the path-adapted Python experiments can be invoked as:

```sh
python3 portable/extended_folds.py
python3 portable/prefix_folds.py 2
python3 portable/prefix_folds.py 3
python3 portable/prefix_folds.py 4
python3 portable/raw_prefix_folds.py 4
python3 portable/symbolic_contexts.py
python3 portable/head_permutation_search.py
```

They require Python 3.10 or later and the standard library. Run without
`-O`, because imported source parsers and checks use assertions. To replay
the first-action scan on the frozen stronger contexts, compile the C++
search source already included one directory above:

```sh
mkdir -p generated
g++ -O2 -std=c++17 ../action_merge.cpp -o generated/action_merge
generated/action_merge ../../construction/inputs/parent195S.native.tm 4 80 data/symbolic_patterns_k4.txt > generated/symbolic_merge_choices.jsonl 2> generated/symbolic_merge_progress.log
```

For a fresh extraction, substitute `generated/symbolic_patterns_k4.txt`
after running `portable/symbolic_contexts.py`. The context extractor uses
the symbolic source executor and its imported block contracts; its context
sets are exploratory search input, distinct from the independent literal
tape audit of the successful 194-state table.
