This bounded extension includes compensating reroutes excluded by the
independent-domain experiment. It uses the same frozen permutation252 table,
SHA256 `939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`,
the same46 states with two external incoming rows, and all251 alternate
working-state targets per row:2,898,046 concrete assignments. The original
Mira-Cult/Jeff/Wade frontend, mira-emmy public253 ancestry and the new
physical-register permutation remain attributed; the frozen table is read-only.

For each deleted state, both incoming targets initially remain unspecified.
A dictionary wrapper interrupts a strict affine trace **before** returning
an unspecified incoming row. The driver branches on that row's251 targets
and restarts the executor from the original case source for every child.
It never resumes an unproved saved symbolic state. A failed trace that reads
no unspecified row is identical for every remaining completion, so that
finite-checker failure prunes the entire corresponding assignment subtree.
This admits assignments whose individual reroutes fail but work together.
It does not treat an interrupted trace as a passing trace.

Every concrete survivor must pass all8391 cases before any literal blank
run. All55 Box-support rows, both literal dispatch96 rows and start64 stay
unchanged. Macro contracts retain their diagnostic mathematical scope; this
Python search does not prove a modified table in Lean. The actual new
logical-to-physical map is `[6,2,0,4,3,7,8,5,1]`. Before the search, all8391
baseline cases and the exact whole82552-step blank boot passed.

The120-second run stopped after120.07seconds. It evaluated136594 partial
assignment nodes and443638 completed affine checks, pruning1,908,549 concrete
assignments. There were no affine survivors, full-recheck candidates or
candidate blank runs. All63001 assignments were excluded for each of30
deleted states:

```text
107 14 32 36 42 49 61 65 66 67 68 72 78 79 81 82 89 92 98
122 125 127 143 149 151 152 153 154 161 166
```

Old167 was partially explored, pruning18519 assignments. The remaining
989497 assignments are represented by247 explicit disjoint frontier nodes
in the permanent JSON. Each node records the deleted state, assigned row
targets, and its number of concrete completions. Every save asserts
`planned = pruned + concrete survivors + remaining`; the final count is
`2898046 = 1908549 + 0 + 989497`. This is a partial search, including15
untouched deletion states. The detailed scratch journal has20160904bytes and
SHA256 `512105b6ff4c535d1a41c60e8b7bba4d125258d549e438ef1d61162759919fad`.

Fuel1000, unsupported symbolic rules and missing-transition failures are
finite diagnostic outcomes, not proofs of semantic impossibility or a state
lower bound. Higher incoming degrees, write/move changes, alternate halting
targets and protected Box-row changes remain outside this family.

Reproduce offline from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_lazy_context_search.py \
  --output Computability/BusyBeaver/Research/ZFC/results/permutation252-lazy-context-search.json \
  --scratch /tmp/zfc-permutation252-lazy-context-search --seconds 120
```

The wall bound can produce a different final frontier on another host. The
saved frontier is the exact scope of this run. No Lean or Coq process runs.

An independent full source review and journal-partition replay passed. Every
branch expansion, traversal order, pruning weight and final frontier was
reconstructed from all136,594 journal entries; the saved247 frontier nodes
matched exactly. This audit did not rerun the affine checks. See
[the review record](results/permutation252-lazy-context-independent-review.json).
