# AX row-order and role-permutation search experiments

This is the portable computational supplement for the new AX scheduling
research. **The recorded searches did not improve the existing baseline and
did not produce a smaller verified Turing machine.** The files contain source
and dictionary-cost experiments, not new binary-machine correctness proofs.

## Recorded results

| Search | Recorded scope | Best recorded result | Interpretation |
| --- | --- | --- | --- |
| AX row-order compression | 12,000 trials; 3,575 distinct orders of the eight rows | Source metrics `(212,10,36)` | 212 source DAG nodes, maximum left-prefix/zero-run measure 10, maximum depth 36; no improvement over the original 203-node source |
| Physical dictionary with row and role permutations | 3,000 proposals | 127 live dictionary rules | Matches the existing 127-rule dictionary; no improvement |

The first count is **12,000 trials**, not 12,000 distinct row permutations.
An order can be retried with a different compression history. Only 3,575
distinct orders occurred. The second count is 3,000 proposals; duplicate
descriptors are not excluded. Neither search is an exhaustive enumeration
of its full transformation family.

The original run summaries and best-result JSON files are copied byte for
byte into `results/axiom_order/` and `results/physical_order/`. Their hashes
are recorded in `pins.json`; portability work did not overwrite them. Tiny
post-adaptation smoke runs are separately stored in `results/smoke_axiom_order/`
and `results/smoke_physical_order/`.

The retained physical-search result contains the field `naive_states: 246`.
This is the bookkeeping sum `119 + 127`. It is **not** the output of a new
binary compilation, a new contextual simulation certificate, or a new
blank-tape bootstrap. Physical decoder sharing can fail in additional entry
contexts even when source expansion and this sum look correct.

## First search: eight logical AX rows

`code/axiom_order_search.py` reads the original 203-node source DAG and the
published pure formula specification. Its assertions identify the exact
logical AX prefix in the expanded source. GEN and the cache-loading prefix
remain first. The eight subsequent logical rows are permuted. The theory
bundle, freshness gate, and cleanup suffix remain fixed.

The eight row lengths in the chosen source-atom representation are
`(67,65,58,61,64,61,72,49)`, the fixed prefix has length 21, and the fixed
suffix length is 752. Each trial changes the row order, then performs a
randomized pair compression across the closed source regions. Its output
metrics describe the emitted source DAG; they do not count Turing-machine
states.

The original run used seed 246018:

```sh
python3 -B code/axiom_order_search.py --runs 12000 --seed 246018 \
  --output results/rerun_axiom_order
```

The supplied full run recorded best metrics `(212,10,36)`. In particular,
the first coordinate remained 212, above the supplied 203-node source. The
search's randomization is a heuristic, and the retained history contains
only successively improved metric tuples rather than every trial.

## Second search: row roles and physical dictionary reuse

`code/physical_order_search.py` imports the first script and the supplied
`closed-sequence-grammar-next22.json` fixture. It verifies that the fixture's
original AST has the same normalized source as the original203 fixture.
It then reconstructs the AX phrase using existing physical dictionary words,
including the distinction between semantic atoms that share physical state
labels but arise in different contexts.

The fixed non-AX dependencies contain 51 dictionary phrases. The original AX
contributes 76 further phrases, giving 127 total. The search combines row
order changes with independent permutations of the parameter roles `a,b,c`
inside each logical row. GEN/cache handling, `h`, `u`, and the fixed AX suffix
retain their stipulated positions or roles. Each proposed dictionary's AX
expansion is checked against the proposed target word.

The original run used seed 7310246:

```sh
python3 -B code/physical_order_search.py --runs 3000 --seed 7310246 \
  --output results/rerun_physical_order
```

The best cost was 127 at trial zero, the original row/role choice. No later
proposal improved it. These source-expansion checks must not be promoted to
a claim that all explored dictionaries implement correct binary runtimes or
have suitable blank initialization.

## Minimal dependencies and portability checks

Both searches need only Python's standard library. This package includes:

- `fixtures/original203.json`, the original source DAG.
- `fixtures/closed-sequence-grammar-next22.json`, the physical dictionary fixture.
- The pinned published formula specification under `fixtures/upstream/`.
- `vendor/theory_backend_experiment.py`, containing only the unchanged
  `published_spec` and `emit` functions used by these searches.

The helper's unused repository-backend imports and unrelated experiments
were omitted. The two retained function bodies are unchanged from the pinned
full ProveIt source. The two search scripts were adapted only at their
input/import/output path definitions; every function body is unchanged.
These claims were checked by comparing Python abstract syntax trees with
source-position attributes removed. Original full-file hashes, adapted hashes,
and origins are in `pins.json`.

After adaptation, each script completed a separate two-trial smoke run.
The first produced two distinct row orders with best `(212,12,37)`; the
second retained 127 dictionary rules. These small runs check portability and
are separate from the supplied full-search records.

```sh
python3 -B code/axiom_order_search.py --runs 2 \
  --output results/new_smoke_axiom_order
python3 -B code/physical_order_search.py --runs 2 \
  --output results/new_smoke_physical_order
```

Do not use Python's `-O` option, which disables the assertions used as checks.

## Small seven-state detector solver attempt

For completeness, `code/synthesize_detector.py` and one small result record
are retained. This is an unchanged prior bounded-synthesis driver with a new
recorded invocation. It needs the optional `z3-solver` Python package, which
is not needed by the two AX searches and is not bundled here.

The recorded invocation used seven working states, a 12-step bound, the
entry/read-one row fixed to return left, first write one, random seed zero,
and a 60-second solver limit:

```sh
python3 -B code/synthesize_detector.py --states 7 --steps 12 --seconds 60 \
  --fix-one --first-write 1 --seed 0 \
  --long-min-read -8 --long-min-exit -8 \
  --output results/detector/new_seven_state_attempt.json
```

The nine cylinder contracts have entry head zero and known right bits
`(+1,+2)=(0,1)`. Short case `k=0,...,7` has its first left one at `-k`, allows
active reads only from `-k` through 2, and requires exact restoration with a
short exit at `-k-1`. The long case has known zeros from -8 through 1, allows
active reads only from -8 through 2, and requires exact restoration with a
long exit at a zero head in `[-8,1]`. Uninspected exterior tape is arbitrary.
The record also states the solver's label-renaming restrictions.

The result was **UNKNOWN because the 60-second limit expired**, using the
recorded Z3 version 5.3.1. It was not UNSAT and supplies no impossibility
result. No accepted seven-state detector or smaller consistency machine was
produced. Large stochastic logs and rejected transition tables are omitted.

## Relation to the mathematical report

The accompanying main report supplies the proposed proof-preserving
transformation principles and their conditions. This supplement records how
two concrete heuristic implementations behaved. It establishes neither
state minimality nor a new PA/Lean consistency endpoint. See `NOTICE.md`
for attribution and the distinction between imported and newly written work.
