# Searches using closed source fragments

These two searches did not produce a machine below 194 working states. They independently revisit a grammar search space broader than the original
190-token AX word; the underlying split-macro strategy already occurs in
earlier packets and is not claimed as new here. Both keep the complete source instruction word fixed and expose internal
closed subroutines as compiler atoms. The first uses 3,966,253 proposal slots;
the second uses 4,215,199. The best fitness remains 134 fixed controls plus 60
effective AX readers, namely 194 working states. Slots can repeat grammars,
propose unchanged terms, or be skipped; they are not counts of distinct machines.

## Search space

The original emitter treats the three copy routines as atoms:

| Routine | Source factorization | Native roots |
|---|---|---|
| Copy D | `node55 = (node49, node54)` | `98 = (19,114)` |
| Copy H | `node58 = (node49, node57)` | `12 = (19,20)` |
| Copy A | `node70 = (node49, node69)` | `166 = (19,179)` |

The first search exposes those common Push prefixes, but preserves the original
three reader roots as free pairs. Association moves can then share a subtree
across a former macro boundary. It also retains the original free two- and
four-increment readers.

The second search additionally exposes these phases:

| Routine | Source factorization | Native roots |
|---|---|---|
| Push | `node49 = (node37, node48)` | `19 = (28,29)` |
| Constructor arithmetic | `node65 = (node17, node64)` | `90 = (105,106)` |

Its scorer reuses every existing fixed control whose two literal transitions
are exactly `(0,R,left)` and `(1,R,right)` for a newly formed pair. This is exact
transition reuse, not a heuristic semantic identification. Dynamic readers are
then allocated and compatible history folds are scored as in the inherited
search engine.

The source fragments are closed in the following precise syntactic sense. A
relative path to a decrement contains a zero, to `continueTo k` contains at
least k ones, and to `breakTo k` contains at least k zeros. Consequently every
conditional or loop transfer is resolved inside the fragment, or exits through
its single fallthrough continuation. Reassociating a sequence of such fragments
preserves the primitive instruction graph after matching corresponding leaves.
`check_source.py` checks these conditions and independently resolves source
addresses. All 60 retained end-of-run grammars have exactly the original 3,673
resolved instructions, including every successor and both decrement branches.
They have not been claimed as newly verified literal machines.

## Reproduction

Python 3 and a C++17 compiler suffice; no repository or network is needed:

```
python3 check_source.py
python3 replay.py --seconds 240 --output /absolute/path/new-search-run
```

To recheck all retained grammar bindings:

```
python3 check_source.py run_copy/*.grammar.json run_phases/*.grammar.json
```

`replay.py` compiles and runs both frozen searches. A shorter budget can be used
for an execution smoke check. Time-limited runs are not expected to reproduce
identical proposal counts across machines. Seeds, input hashes, measured
counts, and limits are in `RESULTS.json`; full logs are `recorded.log` in the two
run directories. The tables encoded in `expanded.txt` use direction 1 for R
and 0 for L. The symbolic atoms and tree are fully encoded in the same file.

## Evidence limits

Fitness includes the inherited scanner-shape restrictions and checks the
compatibility of selected two-cell history folds. A better fitness would still
need independent reconstruction, complete source binding, universal physical
contracts, exact startup, and the consistency calibration. No candidate below
194 reached even the fitness gate here.

The first run uses a conservative increment-marker attribute for its newly
exposed loader atoms. The second uses the inherited recursive attribute
formula exactly and a lower search temperature. These are two different
heuristic runs, not exhaustive searches over the same finite domain. Their
failure implies no lower bound on arbitrary PA-consistency machines.

## Provenance

The baseline sources, fixed table, original grammar, and resolver inputs are
from ProveIt at commit `b5086c8db0f5778b9569c1ce36b7fe0310d5f225`, principally
`Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/` and
`jamesyc-upstream/pa196/PA196/Program.lean`. Search code is adapted from that
packet's `search/search_exact.cpp` and `search/screen.cpp`. The changes are the
closed-fragment input expansion, free fixed-pair reuse, disabling parameter
permutations whose positional offsets no longer apply to the expanded word,
and the stated temperature/pool thresholds. Inherited license notices are in
`licenses/`. `check_source.py` and `replay.py` are new.

## Earlier occurrences of the strategy

The final corpus audit identified the same seven extra atoms in
`pa194_radix_family_2026-11-13/search/split_macro/prepare_split.py`. The three
copy decompositions also occur in
`pa194C_conpa_2026-11-13_2/search/grammar/make_expanded.py`; exact free-reader-pair
reuse occurs in `pa194N_conpa_2026-11-13/research/decoder/screen_nopush.cpp` and
related screens. `PA195_ConPA_research_2026-11-14/axioms/search_split_macros.py`
is an additional precursor. These paths are relative to the filed PA `docs/`
directory. The present code was independently adapted from the primary PA194
search, but the underlying optimization idea is inherited research territory.
The new results here are the actual bounded run receipts, the retained search
endpoints, and the independent source-graph checks, not a new reduction method.
