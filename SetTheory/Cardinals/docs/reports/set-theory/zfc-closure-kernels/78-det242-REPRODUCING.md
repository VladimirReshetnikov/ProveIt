# Reproduction and evidence scope

Run commands from the extracted package root. Python 3.12.14 was used for the
recorded checks. Do not use `python -O`: assertions are part of these ordinary
finite certificate checkers.

## Main checks

```sh
python3 -B code/verify_all.py
python3 -B code/verify_all.py --expanded
```

The first command runs exact reconstruction, two independently implemented
local audits, sparse/dense blank computation, all affine and finite literal
runtime cases, source rotation verification, and the alternative equational
packet checks. The second adds the expanded arbitrary-register runtime.
The supplied `evidence/expanded-runtime.json` is an actual completed expanded
execution, not a forecast based on the affine run. The quick path does not
claim to have re-executed it.

Fresh logs and JSON summaries go to `reproduced/`. An alternate directory can
be selected with `--output DIRECTORY`. The equational check regenerates its
deterministic packet and finite certificates in its own `output/` directory.

Useful individual commands:

```sh
python3 -B code/build_machine.py
python3 -B code/build_machine.py --emit /tmp/detour242-reconstruction
python3 -B code/verify_local_detour.py
python3 -B code/review_detour242.py --package . --output evidence/independent-review.json
python3 -B code/verify_blank.py
python3 -B code/verify_runtime.py
python3 -B code/verify_runtime.py --expanded
python3 -B code/verify_literal.py
python3 -B research/equational1768/verify_exact.py
```

Table files and reference inputs are pinned by SHA256. The expanded record
binds its complete input set before and after the run. It records 8,390 cases,
2,314,880 symbolic rules, 484 covered rows, and no unused row. Exact rule
counts are 1,987,196 literal rules, 322,484 unary-induction rules, and 5,200
finite-list-induction rules. These are symbolic derivation steps, not a
number of concrete Turing-machine steps.

The finite literal suite records 6,473,406 concrete transitions across 8,390
fixtures. For 8,389 returning cases it constructs the expected full source
frame independently. For the sole CH case it compares the final complete
configuration against the exact Combined243 table; both halt after 13 steps.
All fixture records are retained in `evidence/literal-runtime-cases.json.gz`.

The first literal-harness attempt rejected CH's documented null register
field. The checker was corrected to require null only for CH, and the
complete suite was rerun. The short first-attempt log is retained explicitly;
it is not evidence that a machine case failed. Successful current records
bind the corrected checker bytes.

## PDF

```sh
make pdf
```

Requires a standard TeX installation with `pdflatex`, Latin Modern, amsmath,
booktabs, listings and hyperref. `machine/transition_table.tex` is regenerated
from the verified exact canonical table. `evidence/metrics.tex` contains the
reported counts from the supplied successful JSON records. The main report
and its appendix are visually inspected after rendering.

## Optional discovery searches

These are not necessary to verify the selected 242-state machine.

```sh
python3 -B research/local-fold-search/window_invariant.py 8 2
python3 -B research/local-fold-search/search_hybrid_folds.py
python3 -B research/rejected-scanner/shorten_scanner.py
```

The first command constructs a finite abstraction allowing arbitrary tape
at state 95. The second independently validates its initialization and
closure before checking the bounded local-simulation family. It examines
117,612 state-pair/row-choice candidates and certifies three 242-state folds.
Detour242 is the variant retaining 15 and deleting 27. Generated pickle
files are local intermediates; none is needed or supplied as trusted input.
Do not substitute an untrusted pickle file.

The scanner experiment deliberately produces a rejected syntactic candidate.
Its expected result is a failed affine obligation at source index 40, after
56 passing guarded cases. This is a record of a failed approach, not a
component of the selected machine.

`research/source-encodings/RESEARCH_NOTES.md` documents optional grammar and
MILP searches, their dependencies, exact frozen inputs, stopping conditions,
and negative-result scope. Those searches may use a C++ compiler or SciPy;
neither is needed for the main proof and runtime checks.

## Reuse and formalization

The package supplies ordinary mathematical proofs plus executable finite
certificates. It does not contain a serialized internal ZFC proof or a new
Lean/Rocq kernel endpoint. The relative theorem can be formalized by adding
the old-side local invariant, the state map 27 to 15, its exceptional
three-step case, and positive-clock halting transport to the existing ProveIt
machine framework. The exact Combined243 source-to-consistency Lean bridge
retains its pinned open status.
