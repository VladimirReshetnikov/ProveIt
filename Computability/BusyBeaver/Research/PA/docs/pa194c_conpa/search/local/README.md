# Local reductions and source-contract quotient searches

This directory contains the completed optional searches starting from PA194
and PA194C. They produced **no certified 193-state machine**. The four full
source-contract searches tried 460,386 row-choice constructions and executed
1,580,604 symbolic contracts, with no positive preliminary result. These
figures count attempted constructions, including duplicates. They establish
no lower bound and do not prove every candidate semantically invalid.

Read `SEARCH_NOTES.md` for the transformation rules, checking bounds,
arithmetic-box qualification, and further research directions.
`SEARCH_RESULTS.json` binds the input tables and summarizes the observed
results. The individual `*.receipt.json` files and `*.log` files retain the
actual completed search counts. Empty `*.jsonl` result files mean that no
candidate was returned by that particular bounded search.

## Contents

| Files | Purpose |
|---|---|
| `pa194.native.tm`, `pa194C.native.tm`, `pa194AD.native.tm` | Literal native-label input tables |
| `action_merge_all.cpp` | State merging through bounded, exact local detours |
| `incoming_eliminate.cpp` | Delete a state by replacing all of its incoming rows |
| `action_options.cpp` | Export the individually valid local first-action choices |
| `merge_contracts.py` | Quotients choosing each retained row from either old state |
| `expanded_contracts.py` | Additional quotients using the exported action choices |
| `contexts.py`, `contexts194C.py` | Source-specific symbolic observations and blank-start contexts |
| `symbolic_runtime.py`, `Program.lean`, `reconstructed_tree.json` | Standalone PA194 source resolver and inherited symbolic executor |
| `register_coalesce.py` | Coarse zero/nonzero register-allocation analysis |
| `LICENSE.JamesChang`, `LICENSE.ProveIt` | Retained original source licenses |

No compiled binaries or unverified composite machines are included.

## Reproduction

Use Python 3.10 or later, with assertions enabled, and a C++17 compiler for
the C++ searches. Run these examples from this `search/local/` directory:

```sh
python3 -B symbolic_runtime.py
python3 -B merge_contracts.py --family S
python3 -B merge_contracts.py --family C
python3 -B expanded_contracts.py --family S
python3 -B expanded_contracts.py --family C
```

The C-family scripts automatically use the sibling `../../construction/`
directory. They require no external repository checkout. Set the optional
`PA194C_CONSTRUCTION` environment variable only to use a different complete
construction directory. Replaying a search rewrites its local receipt;
elapsed time naturally varies between runs.

The recorded context files and action-choice files are already included.
They can be regenerated using:

```sh
python3 -B contexts.py
python3 -B contexts194C.py
g++ -O3 -std=c++17 action_options.cpp -o action_options
./action_options pa194.native.tm 4 120 symbolic_patterns_k4.txt action_options_S.jsonl
./action_options pa194C.native.tm 4 120 194C_symbolic_patterns_k4.txt action_options_C.jsonl
```

Examples of the broader arbitrary-tape local searches are:

```sh
g++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
g++ -O3 -std=c++17 incoming_eliminate.cpp -o incoming_eliminate
./action_merge_all pa194.native.tm 8 200
./action_merge_all pa194C.native.tm 8 200
./incoming_eliminate pa194.native.tm 8 200
./incoming_eliminate pa194C.native.tm 8 200
```

The arguments after the table are the window radius and maximum local
duration. An optional fourth argument supplies the corresponding-radius
context file. Do not use the radius-four context files with a different
radius. The console progress logs are discovery evidence; they are not a
Lean/Rocq proof or a proof of consistency calibration.
