# Exploratory PA196 physical allocator

This is a finite experiment, **not** a machine smaller than PA196 or a proof of a PA-consistency equivalence. It adapts the U208 source allocator and runtime checker to the separately checked source edits in `../ZERO-TRANSFER.md` and `../SECOND-CLEANUP.md`. The present results establish no new working-state record.

The retained 198-state table is useful only as a conditional root-frame experiment: its 3,810 source instructions pass the inherited symbolic runtime checker at header gap ≥56, with arbitrary nine register values and a nonempty finite spare list. It starts from a supplied correctly encoded root frame. This executable symbolic induction is not a Lean certificate; the theorem that blank-tape startup reaches the edited program's correct root frame, gaps 48–55, and any PA proof or consistency equivalence are **not** established. The blank-tape candidate diverges from the original after 39 steps and has not reached its exact original seed in 10 million steps. This is a bounded observation, not a proof that it never reaches a suitable frame.

## Reproduction and provenance

Run commands below from this directory. Python 3.13.14 and `z3-solver` 4.15.8.0 were used; the latter is required only for allocation, not for the input, witness, startup, or runtime checks. In a disposable virtual environment install `z3-solver==4.15.8.0`. Solver assignments may vary with solver version and iteration order; the saved tables are the exact ones checked. Python's optimized mode must not be used for the symbolic checker, whose inherited engine uses assertions.

The original research archive `docs/incoming/pa208_research_2026-10-29.zip` has SHA-256 `c041198d02709aabe480be7e11a0a96792bad8ffd738a78fc769ccfe26baed5c`. The U208 archive `docs/incoming/U208_ConPA_2026-10-29.zip` has SHA-256 `0662a968902f231ac2483bbd424f80b8f86e6fe1e04bbe97b6f25c634aa532f9`. `allocate_current.py` and `build221.py` adapt `pa208_research/analysis/compiler_upstream/{allocate_current,build221}.py`; `source_language.py` is from that archive's `analysis/emitter/lineage/U209_ConPA_Joint_2026-10-29/code/`. `symbolic_runtime.py`, `independent_runtime.py`, `legacy_mapping.json`, and the runtime wrapper derive from `U208_ConPA_2026-10-29/{code,baseline}/`; the two engines are byte-identical to the U208 archive. See retained upstream notices and licenses in `provenance/`; no blanket relicensing of unspecified-license inherited material is asserted. Upstream authors did not review or endorse these experiments.

`check_inputs.py` reconstructs the native table and all four source inputs from the pinned upstream snapshot and the existing patch code. `independent_inputs.py` separately parses the pinned Lean program and applies the two literal path edits to its flattened leaves, without importing those patch scripts; it checks the exact operation, argument, and path of every input row. The underlying `Program.lean` SHA is `8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872`. The original native table SHA is `454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215`.

```sh
python check_inputs.py
python independent_inputs.py
python witness.py
python check_startup.py
```

For the saved root-frame runtime control and the 198-state candidate, each full runtime command took about two minutes in the recorded environment. They write reports to `/tmp`, not this directory:

```sh
python check_runtime.py --machine pa196.native.tm --sites original.json --mapping legacy_mapping.json --expected-states 196 --output /tmp/pa196-original-runtime
python check_runtime.py --machine two-fresh5/candidate.native.tm --sites two.json --mapping legacy_mapping.json --expected-states 198 --output /tmp/pa196-two-runtime
```

The baseline rederived 4,959 branch cases across 3,812 instructions and covered all 392 rows; the 198-state candidate rederived 4,956 cases across 3,810 instructions and covered all 396 rows. The recorded JSON reports are in `runtime-baseline/` and `runtime-two/`; elapsed times vary. Candidate SHA: `75534c360a43a524382534f4e67bfb556486a68e6d51a1540fd4c75108c372e9`.

## Allocation scope and observed cases

The allocator fixes compatible decoder assignments, permits assignment of remaining nodes to eligible existing rows or a bounded pool of fresh states, and requires the 98 rows in `protected-core.txt` plus compatible helper-trace rows to retain their original transitions; these form 134 protected rows in the recorded runs. It checks source prefix dispatch and reachable state census, **not** preservation of every primitive's runtime. In particular, protected rows do not cover the full execution engine. The inherited alias check was corrected so that a shared state can be fixed at a node if it is compatible with at least one occurrence; occurrence-specific compatibility is then checked on each prefix. The original machine, with zero fresh labels, provides an identity control: `PREFIX_PASS`, 196 reachable states and no transition changes.

All examples used `--feasible-only` and `--protected protected-core.txt`. Each historical receipt records its exact assignments or failure and source SHA. Run this sample by replacing `original.json`, `0`, and the output path with a case in the table:

```sh
python allocate_current.py original.json /tmp/pa196-allocation --protected protected-core.txt --seconds 30 --feasible-only --fresh 0
```

| Source edit | Fresh-state bound | Timeout | Recorded solver result | Resulting reachable states |
| --- | ---: | ---: | --- | ---: |
| Original | 0 | 30 s | SAT, prefix pass | 196 |
| Zero-transfer (`one`) | 0 | 30 s | UNSAT | — |
| Zero-transfer (`one`) | 1 | 30 s | SAT, prefix pass | 197 |
| Site 7 (`two`) | 0 | 30 s | UNSAT | — |
| Site 7 (`two`) | 1 | 30 s | UNSAT | — |
| Site 7 (`two`) | 5 | 30 s | SAT, prefix pass | 198 |
| Both | 0 | 30 s | UNKNOWN (timeout) | — |
| Both | 1 | 20 s | UNKNOWN (timeout) | — |

The UNSATs apply only to the above restricted allocation model and its hard-coded protection and helper requirements; they are not impossibility results for these source programs or for smaller machines. The two combined cases timed out with solver `unknown`, not UNSAT. Historical receipts misleadingly label any non-SAT result `NO_ALLOCATION`; inspect their `solver` field. The copied script changes that display to distinguish `UNSAT` and `UNKNOWN`, without changing constraints. These timeouts and solver results are not guaranteed to reproduce exactly on a different host.

The 197-state `one-fresh1` table has SHA `e5b3a27df424a10a26173365ce58b75bb30e829be656af35cae07943ecc3d3f7`. Despite prefix pass, its symbolic runtime checker stops at case 11, source path `01000`, decrement register 2 on zero: `Unknown run may be empty`. `witness.py` supplies a concrete root-frame comparison with gap 56, all nine registers and first spare zero. The original returns to the correct root frame `0101` after 526 steps; the candidate does not return to that exact frame within 100,000 steps. On the ninth transition, after eight completed transitions, native row `(11,0)` changes from `(write 0, L, 26)` to `(write 0, R, 29)`. This demonstrates the finite prefix screen is insufficient; it makes no claim about the candidate's eventual blank-tape halting.
