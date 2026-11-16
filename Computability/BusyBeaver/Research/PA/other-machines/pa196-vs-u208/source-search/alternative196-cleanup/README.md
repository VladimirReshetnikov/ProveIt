# Source cleanups applied to the shorter-path alternative196

No machine with fewer than 196 states or new `Con(PA)` equivalence was obtained. The supplied alternative196 has 196 reachable working states and maximum source-path length 36. The independent search here applies both previously studied source cleanups to that alternative layout. Its verified startup-preserving candidate for the first cleanup has **197** working states. The evidence below consists of executable checks, not Lean kernel certificates or a proof inside PA.

## Source provenance and checks

The input is `docs/incoming/pa_tm_research_2026-11-13.zip`, SHA-256 `6e6c4840cae029357d9fa47fd204cd953ae5af885e69250048d2941660d6a83f`. `check_archive.py` verifies the archive, the exact extracted members, the 392-row literal/native conjugacy, and the protected startup rows. The alternative literal table SHA is `aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95`; the native archive member SHA (without the locally added `#! start 74` header) is `6a6caa6249fccc7cf8621058f0c7818a77435752a49b8f309629ff3a73ecdbfd`. The supplied alternative `Program.lean` SHA is `abc6f530495511226b17a9a2feff9a015c7bf972de292c241c6a15af0b490411`.

The incoming archive changes the AX head order and association. Its report gives a mathematical head-selection transport argument, but its alternative-specific Lean files were not newly kernel checked and no new PA-internal biconditional was established. The source-specialization checks here assume the **alternative** source begins at site 25 with registers `[2,0,0,0,0,0,0,0,0]`; they do not themselves prove the source's logical relation to PA. The archive's original license and the James Chang license are retained in `LICENSE.research` and `LICENSE.JamesChang`. Inherited allocator and runtime provenance, notices, licenses, and engine hashes are in `../allocator-screen/README.md` and `../allocator-screen/provenance/`.

`independent_inputs.py` parses the pinned alternative Lean source independently and checks every path, operation, and argument in `original.json`, `one.json`, `two.json`, and `both.json`. `verify_zero_transfer.py` and `verify_second_cleanup.py` use two ordinal CFG resolvers and independently replay the abstract invariants from the actual source seed. They show the two source edits retain their old paths and ordinals:

- Replace the subtree at `1010101110` by its right child. The decrement of register 1 at old site 3773 is forced to zero; old sites 3774–3775 are unreachable. The result has 3,809 sites and 160 distinct internal DAG nodes.
- Replace the subtree at `00011` by its right child. The decrement of register 6 at old site 7 is forced to zero; old site 8 is unreachable. The result has 3,810 sites and 161 distinct internal nodes. Combining the edits gives 3,807 sites, 162 internal nodes, and seed site 23.

The register-1 zero/positive closure has 6,275 site/category pairs; the register-6 zero/one/≥2 closure has 9,413 pairs. The nine separate zero/positive screens find only one forced-zero decrement in the whole alternative program, register 1 at site 3773. The `receipts/source-*.json` files pin the complete computed results and source seed dependencies. The CFG projection checks the retained transitions and skips only the proven zero tests. These are finite, checkable certificates of the stated source behavior, not a proof-assistant formalization.

## Startup-preserving 197-state candidate

`candidate197.native.tm`, SHA-256 `917f06ff5a3daa140e1c764010e567614ff18659bf5a5b096a692150768bc368`, is a 197-state physical allocation of the first cleanup. Relative to alternative196, the only changed old row is `(164,1)`, redirected from state 98 to new state 3000; both rows of state 3000 are added. `check_startup197.py` independently compares the whole configurations after each of the first 58,154 blank-tape transitions. The original and candidate runs agree at every step and reach native state 84, source path `100000` at site 25, header offset 48, source register vector `[2,0,0,0,0,0,0,0,0]`, and 26 spare blocks of value 1. Thus the frame satisfies the nonempty finite-spare assumption below.

`check_runtime48.py` uses the byte-pinned inherited U208 symbolic engine with header minimum 48. It rederives all 4,955 zero/positive instruction contracts for the 3,809-site specialized source, with arbitrary natural primary registers and arbitrary nonempty finite spare lists. All 394 candidate rows are covered, counting the generic block lemmas; durations are positive. See `receipts/runtime197-gap48.json`. This executable symbolic induction and concrete startup comparison provide evidence for blank-start physical simulation, but are not Lean or PA proofs. They do not by themselves establish the logical transport from the alternative head order to PA.

## Allocation and bounded local screens

The adapted `allocate.py` uses the alternative native table and source inputs checked above, and uses fresh labels starting at 3000, avoiding the alternative layout's existing 2000-series labels. The unchanged-source identity control returns the original 196-state table with no changed rows. All recorded allocator runs use feasibility mode, `z3-solver==4.15.8.0`, and a 20-second solver limit:

| Source | Protected set | Fresh-state bound | Result |
| --- | --- | ---: | --- |
| First cleanup | Core + helper | 0 | UNSAT |
| First cleanup | Core + helper | 1 | 197-state prefix pass |
| First cleanup | Startup + core + helper | 0 | Empty domain |
| First cleanup | Startup + core + helper | 1 | 197-state prefix pass, candidate above |
| Second cleanup | Core + helper | 0 or 1 | UNSAT |
| Second cleanup | Core + helper | 5 | 198-state prefix pass |
| Second cleanup | Startup + core + helper | 1 | Empty domain |
| Both cleanups | Core + helper | 0 or 1 | UNKNOWN at 20 seconds |
| Both cleanups | Startup + core + helper | 1 | Empty domain |

The allocator has fixed-node and compatible-helper restrictions. Core protection contains 98 original rows; adding the 237 distinct startup rows yields 238 input rows and, with helper traces, 259 protected rows in the startup-preserving runs. The core-only runs protect 134 rows after helper traces. `UNSAT` and empty-domain results apply only to that allocation model, never to all possible Turing-machine layouts. `UNKNOWN` is not UNSAT. A prefix pass alone does not prove runtime correctness or startup; only the saved 197-state candidate above has both additional checks here. Historical receipts include absolute scratch input paths for provenance, but replay needs no such paths.

The literal alternative196 table was also screened with `scan_alt.py`, the local-fold checker specialized to its pinned literal SHA. Its radius-4 blank-window closure has 25,789 abstract configurations and can reach abstract halt. The screen tests local matching on five-cell contexts for up to 16 steps: no direct fold or one-row-patch survivor among 59,064,992 tested patches. See `receipts/folds-window4.json`. This is not a lower bound against other optimizations.

Finally, `scan_rotation_allocations.py` enumerates distinct single **global** rotations of the first-cleanup source with at most 160 internal nodes and the same site-25 path `100000`, verifies the complete ordinal CFG for each, then runs the startup-protected allocator with zero fresh labels. It considers 59 variants. With a two-second solver limit, the original run found 38 UNSAT, 9 empty-domain, and 12 UNKNOWN, and no candidate. The timeout results may vary by host or solver. These are restrictions on this search, not lower bounds for other rotations, allocation models, or machines.

## Reproduction

Run from this directory with Python 3.13.14. Do not use `python -O`, because the inherited symbolic engine uses assertions. The runtime checker takes about two minutes; the fold screen takes about three minutes on the original host. Only allocation commands require `z3-solver==4.15.8.0`.

```sh
python check_archive.py
python independent_inputs.py
python verify_zero_transfer.py
python verify_second_cleanup.py
python check_startup197.py
python check_runtime48.py --machine candidate197.native.tm --sites one.json --mapping ../allocator-screen/legacy_mapping.json --output /tmp/alt197-runtime48 --expected-states 197
python scan_alt.py --table alternative196.tm --invariant blank-window --radius 4 --output /tmp/alt196-folds.json
python allocate.py one.json /tmp/alt197-allocation --protected protected-startup.txt --seconds 20 --feasible-only --fresh 1
python scan_rotation_allocations.py --output /tmp/alt196-rotation-allocations.json --winner-dir /tmp/alt196-rotation-winner
```
