# Discovery programs: replay and scope

These programs preserve the finite search templates used during this investigation. They are **not acceptance certificates for a new consistency machine**. No table in this packet has been verified as a successful construction with at most 217 states. Use the portable verification commands in the packet's top-level `README.md` to check its positive statements and concrete failed interfaces.

All commands below assume the current directory is the **packet root**, containing `inputs/`, `vendor/`, and `experiments/`. Outputs go into fresh replay directories, leaving the supplied receipts unchanged. The final portability review compiled or parsed the programs and checked paths; it did not repeat the discovery searches.

## Self-contained C++ searches

Four programs generate their own finite local test contexts and require only the bundled native primary K218 table. They use standard C++ headers and can be compiled with a C++17 compiler:

```sh
mkdir -p replay/discovery
c++ -std=c++17 -O2 experiments/discovery/scanner_synth.cpp -o replay/discovery/scanner_synth
c++ -std=c++17 -O2 experiments/discovery/scanner_synth_invariant.cpp -o replay/discovery/scanner_synth_invariant
c++ -std=c++17 -O2 experiments/discovery/other_scanner_synth.cpp -o replay/discovery/other_scanner_synth
c++ -std=c++17 -O2 experiments/discovery/phase_reader.cpp -o replay/discovery/phase_reader
```

Run only the searches of interest:

```sh
replay/discovery/scanner_synth inputs/primary218.native.tm > replay/discovery/scanner_synth.hits.jsonl 2> replay/discovery/scanner_synth.counts.txt
replay/discovery/scanner_synth_invariant inputs/primary218.native.tm > replay/discovery/scanner_synth_invariant.hits.jsonl 2> replay/discovery/scanner_synth_invariant.counts.txt
replay/discovery/other_scanner_synth inputs/primary218.native.tm > replay/discovery/other_scanner_synth.hits.jsonl 2> replay/discovery/other_scanner_synth.counts.txt
replay/discovery/phase_reader inputs/primary218.native.tm > replay/discovery/phase_reader.hits.jsonl 2> replay/discovery/phase_reader.counts.txt
```

| Program | Exact scope of its local test |
| --- | --- |
| `scanner_synth.cpp` | Delete state 50; synthesize row 34/0 and one other existing row. Two local boundary contexts, with a 160-transition limit and a narrow known tape window. |
| `scanner_synth_invariant.cpp` | The same mutation family, with a larger known blank region in the exterior case and a later joining state. Two local contexts; 160 transitions. The recorded run produced 207 local survivors, subsequently filtered against source interfaces. |
| `other_scanner_synth.cpp` | Delete, in turn, states 34, 23, 15, 9, 5, and 3. Synthesize the predecessor's zero row and one borrowed row. It checks the listed finite zero-run contexts, with a 240-transition limit. |
| `phase_reader.cpp` | Delete state 50 and fix the proposed writer changes at 41/0 and 24/0. Synthesize 41/1 plus one additional row, against eight local contexts for the two active phase modes. It uses a 120-transition limit. |

Survivors are written as JSON lines to standard output; counts go to standard error. A local survivor still requires ordinary source uses of the changed rows to be checked. An empty survivor file is not a proof of a state lower bound. The searched second-row positions are restricted by the failing traces and the explicit exclusions in each program.

These drivers use the native state labels, including dispatch 84 and halt 254, and fixed arrays sized for the supplied tables. They do not validate arbitrary alternative table formats or missing files. Use the exact bundled input path above; a vacuous run on a missing input must not be treated as a search result.

## Portable Python finite replays

The following three drivers were adapted to use `inputs/`, the bundled `vendor/runtime/independent_runtime.py`, and the supplied survivor lists. They require Python 3.10 or later and the standard library. Each accepts an optional **fresh output directory** and refuses to overwrite an existing directory:

```sh
python3 -B experiments/discovery/scanner_effects.py replay/scanner-effects
python3 -B experiments/discovery/filter_scanner.py replay/scanner-filter
python3 -B experiments/discovery/filter_phase.py replay/phase-filter
```

Omitting the argument writes under `experiments/replay/PROGRAM_NAME/`.

- `scanner_effects.py` removes state 50 and changes 34/0 to `0 L 75`, then records failures against all primary source guards. It uses zero-valued registers, toggles the tested decrement register to one for its positive case, and supplies one zero spare block. Its per-case limit is 5,000 transitions.
- `filter_scanner.py` reads `experiments/receipts/scanner_invariant_hits.jsonl` and filters those already supplied local survivors against the primary source guards, in its recorded priority order. Its per-case limit is 4,000 transitions.
- `filter_phase.py` reads `experiments/receipts/repair_phase_hits.jsonl` and filters those already supplied row repairs, in its recorded priority order. Its per-case limit is 5,000 transitions.

The filters stop at the first halt or **clean** dispatch frame, rather than any visit to state 84. They compare the expected head and entire finite one-cell set; this fixes all cells outside that set to zero. The guard samples do not quantify over arbitrary register values, spare lists, or gap sizes. A limit failure means the bounded test did not establish the requested outcome. These replays do not establish blank-run nonhalting or equiconsistency. If a future input list produces a finite survivor, its emitted table is explicitly named `unverified-...native.tm`.

## Historical drivers with additional dependencies

The remaining programs are retained as research provenance. They are **not complete standalone replays from this archive**. Their historical input contexts or checkout layout must be restored before execution. No commands below are implied to reconstruct missing data.

| Program | Additional requirements and status |
| --- | --- |
| `repair77.cpp` | A native table and a second file of decimal unsigned 64-bit tape masks. Each mask specifies an ordinary state-77 source context; the program adds its scanner context internally. The exact historical mask file is not bundled. Limit: 160 transitions. |
| `repair108.cpp` | The historical marker-relay table and a second file containing `initial_mask goal_mask goal_state goal_head` per case. Neither the exact relay table nor this context file is bundled here. Limit: 100 transitions. |
| `repair_scan_phase.cpp` | A native table plus a counted full-frame case file. Each case contains `ordinal positive expected_head initial_count expected_count`, followed by the initial and expected one-cell coordinates. The selected historical cases are not bundled in this numeric format. Limit: 2,500 transitions; it searches one repair row after shortening the scanner. |
| `filter_other_scanner.cpp` | A native table, a counted full-frame case file in the preceding format, and a counted numeric survivor file containing `id drop entry_state write direction target patch_state patch_bit patch_write patch_direction patch_target`. The numeric input files are not bundled; the JSON outcome receipt does not replace them. Limit: 5,000 transitions. |
| `allocate217.py` | NumPy, SciPy with `scipy.optimize.milp`, the historical ProveIt pricing modules `source_language.py` and `build221.py`, the extracted dominated-rho8 report, and a workspace with `root_work/`. It reads or constructs `root_work/dominated_phase_protected.json`. Its arguments are a source JSON file and an output directory. The retained version protects engine rows and the detours of retained source roles. |
| `global_role_allocate.py` | The same external pricing modules, dominated source/table, NumPy/SciPy, and the already constructed `root_work/dominated_phase_protected.json` cache. Its arguments are a source JSON file and an output directory. It models all source interior roles, with anonymous ordinary decoder states and an empirical fixed engine. |

The two allocation scripts still resolve their historical workspace relative to their original `root_work/` location. Running them in this `discovery/` directory without adapting those paths will not restore that workspace. The packet's `source-layout/source_language.py` supplies source utilities, but it does not supply all the missing `build221.py` compiler interfaces or the historical cache/layout. The allocator limits are 30 and 45 solver seconds respectively; solver version, tie-breaking, and time limits can change the chosen allocation.

The allocators also include hypothesized generic primitive entries, including right-hand CI5 and CI6. A solver optimum is only an optimum of the stated finite constraint model. A decoder-prefix pass does not prove those primitive entries correct: the supplied 220-state equality/scanner experiment passes prefix binding and still has concrete primitive-interface failures. No solver receipt here is a certificate for a successful new machine.

## Evidence hierarchy

The discovery outputs should be interpreted in this order:

1. A source CFG certificate establishes the specified source semantics, independent of register magnitudes.
2. A finite local join or finite primitive test checks only its explicit contexts and limits.
3. A concrete mismatch at a clean interface refutes that particular interface contract; a search timeout or missing bounded join does not prove inequivalence.
4. A quantified binary simulation and a valid blank-start calibration are separate obligations.
5. A consistency-machine claim additionally needs the logical translations connecting its calculus with ZFC.

The packet's rejected tables and negative receipts are kept to expose the failed obligations, not to suggest that high partial coverage permits those obligations to be omitted.
