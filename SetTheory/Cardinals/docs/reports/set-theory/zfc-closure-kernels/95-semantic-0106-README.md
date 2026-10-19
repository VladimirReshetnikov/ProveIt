# Transition and grammar experiments against routing245

**No machine below 245 states is established by these experiments.** This
directory contains reproducible finite searches, their frozen inputs and
results, and a sound arithmetic source rewrite with a 245-state realization.
It is intended as a component of the ProveIt research archive. The main
report provides the logical reduction and the independent counterexamples.

The baseline is the existing routing245 machine from ProveIt commit
`6d69a46dce1de15397a9d2448dcc946d08c90327`. Its literal original-label table is
`reference/baseline245-old.tm`. It has 245 working states and 490 rows, starts
in state 95, uses dispatcher 96, and has halting label 254. Its highest working
label is 255; a label is not a state count. The byte SHA256 of this table is
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.
The normalized table in the enclosing archive has different bytes and labels.

## Fast independent checks

Run from this directory using Python 3.10 or newer:

```sh
python code/rebuild_fixtures.py
python code/check_fine.py inputs/fine/input.json results/fine/result.json
python code/check_fine.py inputs/fine/expanded-input.json results/fine/expanded-result.json
python code/check_route_grammar.py results/new-zero6-k127.json --inputs inputs --bootstrap-lock inputs/bootstrap-lock54.txt
python code/audit_hg_swap.py --affine
```

The fixture builder independently parses the retained original source,
checks every ordered leaf against the current routed tree, transfers the
retained finite register fixtures, and rebuilds every byte of the compressed
input. It also checks the baseline table identity and the pair/elimination
recipe counts. The compressed fixture is about 440 KB; the decompressed file
is about 25 MB. Its decompressed SHA256 is
`71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1`.

The fine-grammar checkers establish finite syntactic facts, including exact
fine-token equality, orientation, reachability of every grammar rule, and
the pointer-shape bounds. The coarse checker is inherited and still prints
the historical 118-role framework accounting. The maintained short-scanner
framework has 117 roles. The checker does not build a machine; neither its
historical total nor a filename containing `k127` establishes a state count.
The serialized successful grammar count remains128.

## Finite transition searches

All these searches use the same 8,385 finite instruction fixtures, generated
from the inherited invariant. These fixtures cover all 490 table rows. The
baseline takes at most 2,686 binary steps per fixture. The screen allows
20,000 steps per fixture and tape coordinates from −64 through 1983. Initial
frames have gap 181 and 167 spare blocks, each with value 1.

The fixtures are representative configurations, not claims that every
configuration is reached on the actual blank run. A timeout or excursion
outside the allocated tape means failure of the stated bounded screen;
it is not a proof of mathematical inequivalence. Even a full survivor would
require a universal simulation and a separate blank-start check.

| Search | Recipes | Passed preliminary probes | Passed full screen |
| --- | ---: | ---: | ---: |
| Pair identification, exact target | 119,560 | 54 | 0 |
| Single-entry elimination, exact target | 133,712 | 24 | 0 |
| One further row repair, exact target | 3,499,936 | 22 | 0 |
| Pair identification, arbitrary legal spares | 119,560 | 54 | 0 |
| Single-entry elimination, arbitrary legal spares | 133,712 | 24 | 0 |
| Pair identification, translated legal frame | 119,560 | 54 | 0 |
| Single-entry elimination, translated legal frame | 133,712 | 24 | 0 |
| One further row repair, translated legal frame | 3,499,936 | 22 | 0 |

These families overlap and must not be added together as distinct machines.
Counts are recipes, so two recipes can describe the same table. The scopes
are as follows:

* **Pair identification:** choose an unordered pair of working states. For
  each read symbol, choose the surviving row from either original state,
  then redirect destinations of the removed state to the survivor. This is
  `4 * binom(245,2) = 119560` recipes.
* **Single-entry elimination:** exclude start 95 and dispatcher 96. There are
  137 remaining states with exactly one external incoming transition; a
  self-loop is not an external entry. Redirect that entry to any surviving
  working state with either write symbol and either direction. Halting
  destinations are outside this search. The count is
  `137 * 4 * 244 = 133712`.
* **One further repair:** retain the 24 near-eliminations from the exact
  preliminary screen. For each, inspect the visited rows of its first bad
  fixture trace. Change one further visited row, other than the removed
  state or the first edited row, using the same write/direction/destination
  choices. There are 3,499,936 recipes. This is not an exhaustive search over
  all two-row repairs. Both repair runs use this same retained 24-element set.

Exact-target filters compare the entire tape and head at dispatcher return.
The `weak_` filters preserve the exact head, header, encoded pointer and
nine primary registers but permit any valid nonempty finite spare suffix.
The `frame_` filters additionally permit translation of the whole frame and
any output gap at least 181. They still preserve the expected pointer and
all nine registers and require the remainder of the left tape to be blank.
This last finite threshold is 181, **not** the universal gap 64 theorem in
the report. The JSON field `full_literal_pass_count` is retained in the
relaxed variants, where it means acceptance by their explicitly relaxed
filter.

### Reproduce transition counts

The programs require a C++17 compiler. Each writes its summaries into the
current working directory. The repair program consumes `near-eliminations.txt`
written by the exact elimination program.

```sh
mkdir -p work
python code/rebuild_fixtures.py --output work/cases.txt
c++ -O3 -std=c++17 code/pair_merge.cpp -o work/pair_merge
c++ -O3 -std=c++17 code/eliminate_search.cpp -o work/eliminate
c++ -O3 -std=c++17 code/repair_search.cpp -o work/repair
c++ -O3 -std=c++17 code/weak_resource_merge_search.cpp -o work/weak_merge
c++ -O3 -std=c++17 code/weak_eliminate_search.cpp -o work/weak_eliminate
c++ -O3 -std=c++17 code/frame_resource_merge_search.cpp -o work/frame_merge
c++ -O3 -std=c++17 code/frame_eliminate_search.cpp -o work/frame_eliminate
c++ -O3 -std=c++17 code/frame_repair_search.cpp -o work/frame_repair
cd work
./pair_merge cases.txt
./eliminate cases.txt
./repair cases.txt
./weak_merge cases.txt
./weak_eliminate cases.txt
./frame_merge cases.txt
./frame_eliminate cases.txt
./frame_repair cases.txt
```

On the recorded machine, the pair/elimination screens took about 10–13
seconds each. The exact and translated-frame repair runs took 256 and 279
seconds. Elapsed time varies by machine; the enumerated recipe counts are
the meaningful reproducibility targets.

## Grammar heuristics

The reported runs use the exact frozen input files. They are stochastic
searches stopped by elapsed time, so rerunning a seed on another machine
does not guarantee identical iteration counts or final grammar syntax.

| Run | Proposals | Accepted | Restarts | Budget | Best total rules |
| --- | ---: | ---: | ---: | ---: | ---: |
| Coarse words, 54 bootstrap locks | 28,351,400 | 9,493,501 | 480 | 900s | 128 |
| Fine words | 11,433,285 | 3,714,950 | 514 | 600s | 128 |
| Fine words, canonical expansion moves | 9,245,823 | 2,994,213 | 419 | 480s | 128 |
| Sound `gm → hg` source variant | 9,717,819 | 3,257,549 | 165 | 300s | 128 |

The coarse run has 48,157 accepted uphill moves; the `hg` run has 16,925.
The fine runs keep 51 shared rules fixed and search the 77 private rules of
the axiom builder. Their free dictionary has 95 words over 30 fine atomic
pieces, and the target has 1,270 fine tokens. The expanded run additionally
permits 141 canonical decompositions taken from the source. Both resulting
fine grammars emit 682 coarse calls and pass the finite independent checks.
The optimum in these heuristic search spaces has not been proved.

From this directory:

```sh
mkdir -p work
c++ -O3 -std=c++17 code/anneal_routes_zero6.cpp -o work/anneal_routes
c++ -O3 -std=c++17 code/fine/anneal.cpp -o work/anneal_fine
c++ -O3 -std=c++17 code/fine/anneal_expanded.cpp -o work/anneal_expanded
work/anneal_routes inputs/route-grammar.txt inputs/route-constraints.txt work/coarse.json 900 9810471 127 inputs/bootstrap-lock54.txt inputs/resume-k128.txt
work/anneal_fine inputs/fine/input.txt work/fine.json 600 8261761
work/anneal_expanded inputs/fine/expanded-input.txt work/expanded.json 480 137291
work/anneal_routes inputs/hg-swap/grammar.txt inputs/hg-swap/constraints.txt work/hg.json 300 2184527 127 inputs/hg-swap/boot.txt inputs/hg-swap/resume.txt
```

`code/fine/prepare.py --output work/rebuilt-fine` reconstructs the semantic
fine-word inputs from the retained source metadata. Its iteration order was
made deterministic for packaging. JSON dictionary order can therefore differ
from the original frozen input; semantic contents agree. Use the frozen
`inputs/fine/*.txt` for reproducing the recorded searches.

## A sound arithmetic rewrite with a 245-state table

Let `g` transfer all of register X into H, `m` increment H, and `h` increment X.
For every natural pair `(x,h0)`, both `gm` and `hg` terminate with
`(X,H)=(0,h0+x+1)`. All other registers are unchanged. These are closed
regions, so replacing them preserves the surrounding source computation
by a finite stuttering argument. The proof is in
`notes/closed-macro-identities.md`.

`results/hg-swap/hg245.tm` changes only the two outgoing rows of state 142.
It has 245 working states. `code/audit_hg_swap.py` checks the exact source
replacement at all four expanded occurrences and replays 416,557 blank
steps using independent sparse and dense tapes. The resulting frame has
head −5, header 178, gap 183, logical registers `(3,0,0,0,3,0,0,0,0)`, and 169
spare blocks of value 1. Its table SHA256 is
`461a3184d03e72f3147f60aaf582efee66d950b977df45aa85aac43bafb773a1`.

The optional `--affine` audit checks all 8,391 guarded primitive instructions
with padding 64 and universally quantified additional padding, under the
unchanged inherited register-box contracts. It checks every register vector
satisfying the relevant guard. It does not reprove those contracts or
provide a new proof-assistant endpoint. The source still has 6,460 leaves,
maximum depth 51, and maximum zero run 6.

This audited literal table uses the baseline grammar with the two state 142
row edits. The final `results/hg-swap/result.json` from the 300-second search
is a different, abstract 128-rule grammar with properties `(3,6,52)`. It has
not been compiled into an audited binary table. The literal table's affine
certificate does not apply to that final search grammar.

The tempting `gm → m` replacement is different: it fails to clear X on one
inequality branch. The independent counterexample in the enclosing archive
shows that this corrupts a later freshness comparison. No rejected 244-state
table is presented here as a valid consistency machine.

## Provenance and organization

`results/summary.json` consolidates the recorded counts; raw terminal logs
and per-search summaries are retained. `reference/prior-PROVENANCE.json`
belongs to the inherited routing245 package, not to a new claim of proof
assistant compilation. `NOTICE.txt` and `licenses/` retain source attribution.
All script dependencies required by the commands above are included.
