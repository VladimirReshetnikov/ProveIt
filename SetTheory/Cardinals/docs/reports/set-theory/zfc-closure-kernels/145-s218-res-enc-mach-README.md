# Machine-side search package

**Status: no verified machine with 218 states or fewer was found.** This folder records reproducible searches, source invariants, and rejected encoding routes. The two validated 219-state variants are in the main packet's `machines/` directory and are checked by its separate verification replay.

Read [SEARCH_REPORT.md](SEARCH_REPORT.md) for the methods, exact scopes, counts, and limitations. `search_summary.json` aggregates completed receipts. Recorded results live in `receipts/`; reruns write to `output/`.

## Quick replay

Run from any directory:

```sh
python3 /path/to/research/encoding/machine/replay.py
```

Python 3.10 or newer and a C++17 compiler are sufficient. The default verifies all packaged file hashes, recomputes source abstract invariants and CFG/liveness facts, and reruns the physical compiler on the identity register assignment. The identity result must reproduce the exact 219-state baseline table hash. This is a calibration of the exploratory compiler, not a proof that its nonidentity outputs are correct.

## Optional searches

These commands intentionally run substantially more work:

```sh
python3 replay.py --mode finite --screen bisim_general --seed baseline
python3 replay.py --mode finite --screen bisim_choice --seed nop
python3 replay.py --mode finite --screen liveness_general --seed baseline
python3 replay.py --mode finite --screen finite_bypass --seed baseline
python3 replay.py --mode local --local fold7
python3 replay.py --mode local --local double
python3 replay.py --mode equality
python3 replay.py --mode permutations
python3 replay.py --mode joint
```

The finite screen names are the corresponding C++ filenames without `.cpp`. See `--help` for all choices. The source graphs, class assignments, and admitted backgrounds are regenerated for the selected seed. Every finite screen calibrates its seed on the complete selected suite before testing mutations.

The joint-pattern computation uses roughly half a gigabyte of memory. The local radius-7 invariant and equality grammar node files can also be sizable. They are generated rather than included. The equality cost-7 grammar intentionally omits the cost-6 intermediate layer, as described in the report, so it is not an exhaustive size-seven search.

The `row160` and `both` seeds are exploratory finite-passing mutations. They are not given an unbounded runtime theorem. The `nop_rho6` seed is a composition used for search and is likewise not represented here as a newly certified machine. Baseline, NOP, and rho6 provenance and the separately checked two latter machines are explained in the main packet.

## Source and provenance

`data/k219` contains the small literal baseline inputs. `support/k221/portable` contains the inherited source-language and decoder-binding utilities. `provenance.json` records both original and packaged hashes for path-adapted Python scripts; the C++ search programs were copied without semantic changes. `manifest.json` covers all distribution files except itself. No binaries or Python bytecode are distributed.

The failed raw 219-state halt specialization is deliberately excluded as a candidate table. Its source transformation is valid, but its naive physical compilation overwrote protected engine row 38/0. The explicit CI5 failure and the source invariant are documented in the report and the sibling audit folder.
