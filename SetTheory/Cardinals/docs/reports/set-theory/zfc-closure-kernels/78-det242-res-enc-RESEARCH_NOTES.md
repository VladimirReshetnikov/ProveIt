# Bounded source-encoding experiments

These experiments found no replacement source grammar below 128 charged grammar
roles and no additional Turing-machine reduction. They are auxiliary research
artifacts for the separate 242-state detour construction. None of the JSON search
dictionaries in this directory is certified here as a runnable blank-tape Turing
machine.

## Inputs and provenance

The source and routing constraints are those of the original 245-state routed
baseline, before the QT rotation used in the combined 243-state machine. Thus the
complete finite source expands to **6,460 leaves** here; the rotated source has
6,459. A grammar role is one charged binary word-decomposition node. Grammar role
counts alone do not give a complete machine-state count.

The upstream research files were recovered from the source-71 bundle
`zfc244-loop-rotation-20261018`, which is incorporated under `docs/incoming` in
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming).
The current construction is documented in
[candidate-combined243](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/candidate-combined243/README.md).

Copied upstream inputs:

- `anneal_cluster.cpp`: `research/grammar/anneal_cluster.cpp`.
- `fine-grammar.txt`, `fine-constraints.txt`, `fine-lock54.txt`:
  `research/grammar/fine/`.
- `baseline_fine_grammar.json`, `baseline_resume.txt`: the original
  `reference/baseline245/grammar.json`, with macro words translated to the closed
  fine-token vocabulary using the matching 44 terminal rows of the semantic and
  fine grammar inputs. This translation preserves word identities and the
  terminal orientation masks.

The raw `fine-grammar.txt` parse has maximum zero run seven. It is an input word
dictionary, **not** the valid shortened-scanner baseline. The explicit resume
file restores the routed baseline with properties `(3, 6, 51)` (leading zeros,
maximum zero run, maximum source depth). The unrelated
`reference/normalized245_grammar.json` uses a modified DNE source and was not
silently substituted for this baseline.

New work consists of `exact_exchange.py`, `milp_dictionary.py`, `make_pool.py`,
`audit_inputs.py`, `make_zero5.py`, and the eight-projection `reduced-locks.txt`.
`anneal_zero5.cpp` is generated from the upstream engine by `make_zero5.py`.

## Recorded results

| Experiment | Budget / explored neighborhood | Result |
|---|---:|---|
| Baseline routed annealing, seed 21891 | 300 s; 4,833,090 proposals | Best 128 roles |
| Reduced bootstrap locks, seed 172957 | 600 s; 9,603,771 proposals | Best 128 roles |
| Soft six-zero penalty, seed 621719 | 600 s; 5,367,266 proposals | Best score at 133 roles and nine offending source paths |
| Exact exchanges, original baseline | All 4,005 single/pair erasure sets from 89 eligible definitions; 1,176 fresh-word trials | No smaller grammar in this neighborhood |
| Exact exchanges, second 128-role parse | Same 4,005 erasure sets; 681 fresh-word trials | No smaller grammar in this neighborhood |
| Historical dictionary-union MILP | 252 words; 377 parse choices; 120 s | Returned 128-role parses violating the source zero-run bound; no accepted witness |
| Historical expanded MILP | 642 words; 2,163 parse choices; 180 s | No incumbent for the target of at most 127 roles before timeout |
| Frozen final-input MILP | 657 words; 2,205 parse choices; 30 s | No incumbent for at most 127 roles before timeout |

The raw-input control search completed 7,138,630 proposals in 300 seconds but
accepted no moves; it retained the zero-run-seven raw parse. It contributes word
labels to the later finite pool and provides no positive evidence for a valid
machine.

`input_audit.json` is a fresh expansion of every saved final dictionary. In
particular:

| Saved dictionary | Roles | Maximum depth | Maximum zero run | Paths with six consecutive zeros | Broken original bootstrap projections |
|---|---:|---:|---:|---:|---:|
| Baseline | 128 | 51 | 6 | 50 | 0 |
| Second baseline parse | 128 | 44 | 6 | 50 | 0 |
| Reduced-lock result | 128 | 49 | 6 | 46 | 10 |
| Soft-penalty result | 133 | 63 | 6 | 9 | 0 |

Every listed final dictionary preserves all 22 route projections and expands to
6,460 source leaves. The reduced-lock result intentionally changes ten of the
54 original bootstrap projections; it therefore needs a new complete boot
construction and is not a candidate machine. The soft-penalty result still has
nine six-zero paths, so it does not justify deleting the next scanner state.

## Neighborhoods and limitations

The exact exchange experiment retains the root words, current route-entry words,
bootstrap projection sources, and bootstrap projection targets. It deletes at
most two other shared definitions, reparses their direct consumers jointly, and
introduces at most one new word whose two children already exist. Both records
show zero branch-cap hits and zero complete route-compatible assignments in that
neighborhood. This is not a lower bound on arbitrary grammars, source rewrites,
or Turing machines.

The modified annealer scores a dictionary by its role count plus 0.30 times the
number of source paths containing six consecutive zeros. The path counter uses
a finite dynamic program indexed by the number of trailing incoming zeros. This
turns the difficult scanner-five goal into a graded search objective. The result
is a useful partial reduction of offending paths but fails the required final
constraint.

The MILP chooses word roles and binary decomposition cuts simultaneously. Child
closure, orientation masks, and the one- and two-bit route projections are
explicit binary constraints. Optional height variables bound leading zeros,
maximum zero run, and expanded source depth; an independent finite expansion
checks any returned dictionary. This is a finite-pool model. HiGHS solver status
and floating-point objective values are recorded as computational observations,
not as formal lower-bound certificates. In particular, **timeout is not
infeasibility**.

The two historical MILP jobs read intermediate annealer outputs while that search
was still running; those exact intermediate dictionaries were not snapshotted.
Their logs are retained as observations, not advertised as byte-reproducible
runs. `milp_frozen.json` records a separate 30-second bounded run using the final
included inputs and regenerated repeated-word pool. The included scripts and
input manifest make this latter model reproducible. Search trajectories use
wall-clock budgets, so fixed random seeds alone do not guarantee identical
iteration counts across machines.

## Reproduction

Run these commands from this directory. Python 3 and a C++17 compiler suffice for
the exact exchanges and annealers. The MILP additionally requires NumPy and
SciPy with `scipy.optimize.milp`.

```sh
python audit_inputs.py
python exact_exchange.py --output reproduced_exchange.json
python exact_exchange.py --input search_baseline.json --output reproduced_plateau_exchange.json
python make_pool.py
python milp_dictionary.py --seconds 30 --height-model --feasible-target --relaxed --pool baseline_fine_grammar.json search_control.json search_baseline.json search_reduced_locks.json search_zero5.json pool_repeated.json --output reproduced_milp.json
```

The longer stochastic experiments can be rerun without overwriting the included
records:

```sh
c++ -O3 -std=c++17 anneal_cluster.cpp -o anneal_cluster
./anneal_cluster fine-grammar.txt fine-constraints.txt reproduced_baseline.json 300 21891 127 fine-lock54.txt baseline_resume.txt
./anneal_cluster fine-grammar.txt fine-constraints.txt reproduced_reduced.json 600 172957 124 reduced-locks.txt baseline_resume.txt
python make_zero5.py
c++ -O3 -std=c++17 anneal_zero5.cpp -o anneal_zero5
./anneal_zero5 fine-grammar.txt fine-constraints.txt reproduced_zero5.json 600 621719 128 fine-lock54.txt baseline_resume.txt
```

The promising remaining direction is a source/grammar change that removes all
remaining six-zero paths while retaining at most 128 grammar roles. That is a
specific unachieved target, not evidence for a 241-state machine. Any future
success must rebuild the machine, validate its complete initialization, and
replay the changed routing and runtime contracts before it can be composed with
the proved local detour.
