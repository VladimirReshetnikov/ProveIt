# Fixed-controller and startup searches

**Status: no accepted machine with fewer than 194 working states.** This bundle records bounded negative searches and a source-level reassociation. It does not establish a new nonhalting/consistency equivalence. All state counts exclude the unique halting control, and all machines are binary, one tape, with left/right moves.

## Provenance and reproduction

Inputs are copied from VladimirReshetnikov/ProveIt commit
`75a42a28ca818627f5a104fb0f0c7f7d02a52947`:

- `Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/construction`: compiler, symbolic executor, primary grammar, dense table, native-label map.
- `Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean`: fixed source tree.

`manifest.json` gives SHA-256 digests of every supplied input and script. The compiler and executor are inherited code. The research scripts and this README were prepared for the present comparison. Copyright/license notices for the copied material are in `licenses/`.

Python 3.10 or later, standard library only; assertions must be enabled. From this directory:

```sh
python scripts/reachable_rows.py
python scripts/rotation_screen.py
python scripts/repair_root_history.py
python scripts/probe_scanner_startup.py
python scripts/probe_startup_variants.py
```

Each script overwrites only its receipt(s) in `receipts/`. The bundled subset of the upstream compiler supports these commands; it is not a complete upstream checkout and does not support every unused compiler entry point. These checks are executable evidence, not new Lean kernel proofs or a general-purpose certified interpreter.

## 1. Conservative source reachability

`reachable_rows.py` starts at the established clean source boundary, ordinal 25, with logical registers `[2,0,0,0,0,0,0,0,0]`. Its finite abstraction records whether each of nine registers is zero or positive. A decrement of a positive register nondeterministically leaves that register positive or makes it zero, so the closure overapproximates reachable stores.

Results:

| Quantity | Value |
|---|---:|
| Reached source-site/positivity-mask pairs | 263,888 |
| Reached source sites | 3,671 / 3,673 |
| Retained source instruction outcomes | 4,777 / 4,780 |
| Literal transition rows protected or observed | 388 / 388 |
| Rows observed during exact startup | 237 |
| Direct row-compatible state merges | 0 |

The excluded outcomes are the positive branch at source site 3634 and sites 3635–3636. The script checks the exact full startup tape after 58,154 steps. It then records rows visited by the inherited symbolic executor on eligible instruction contracts, conservatively includes all protected register-operation rows, and includes the startup rows. No row becomes a don't-care under this screen. This does not rule out multirow changes, different invariants, or a different compiler.

Full output: `receipts/screen.json`; the complete finite closure is `receipts/masks.json`.

## 2. Two source reassociations

The proposed changes to the fixed source DAG are:

```text
node21  = (node20, node170)
node171 = (node21, node23)
node172 = (node7, node171)
node162 = (node37, node163)
node164 = (node75, node162)
```

All 3,673 resolved instructions, including every successor ordinal, are exactly equal before and after these reassociations. The first source address changes from `000000` to `00000`. Outside the AX emitter (source ordinals 50 through 3553), no new address contains six consecutive zeros, and no increment address contains five consecutive zeros.

This is a source-level result. A physical reader can have additional incoming-history requirements. Native state 69 is shared by `node20` and `node72`; the rotation changes the incoming bit at `node20` from 1 to 0 and invalidates that sharing. Updating the fixed reader rows also invalidates some inherited AX-fold uses of those rows.

`rotation_screen.py` checks four diagnostic tables against all 4,780 inherited symbolic source outcomes:

| Diagnostic | Working states | Failed outcomes | Failed fixed-region outcomes |
|---|---:|---:|---:|
| Rotations, seven-zero scanner, inherited readers | 194 | 11 | 3 |
| Same, plus standalone reader 333 for `node20` | 195 | 8 | 0 |
| Rotations, six-zero scanner, inherited readers | 193 | 50 | 3 |
| Same, plus standalone reader 333 for `node20` | 194 | 47 | 0 |

The six-zero scanner deletes native state 34 and replaces `(23,0)` by `0 L 75`. The extra reader has rows `0 R 105` and `1 R 31`; the rotation's `(53,0)` row enters it. The 193-state diagnostic is **rejected by the supplied checks**, not a proposed solution. The exact failed outcomes and row edits are in the script and `receipts/rotation_screen.json`. This bundle intentionally does not present a failed diagnostic table as an accepted machine.

## 3. Bounded history-repair search

`repair_root_history.py` tests all 776 replacements of row `(69,0)` using an existing state as target: two written symbols, two directions, and 194 targets. It screens the 38 source contracts whose original symbolic executions encounter state 69. No replacement survives. The seven-zero scanner remains in use during this search.

This exhausts that one-row template only. It does not rule out changes to other rows, adding or repurposing a helper, a different grammar, or a larger-window simulation. Receipt: `receipts/root_history_repair.json`.

## 4. Bounded blank-start experiments

`probe_scanner_startup.py` probes thirteen existing start controls for at most 200,000 steps on the rotated, six-zero diagnostic with extra reader 333. Runs with fewer than three one-cells are stopped after the head moves beyond distance 5,000. The run starting in native control 198 halts after 25 steps. None of these observations provides a consistency calibration. First and last parsed source-format frames are retained in `receipts/startup_probes.json`.

`probe_startup_variants.py` uses the ordinary start control 74 and compares the rotated six-zero and seven-zero diagnostics, both with reader 333. Neither reaches a parsed source-ordinal-25 frame having `N >= 1` and all eight other logical registers zero within 5,000,000 steps. Neither halts within that bound. Frame parsing checks the entire finite support of the tape, permits every header-gap size, and records at least ten physical registers; it does not impose an upper bound on the gap. The old AX grammar and folds are retained, so these are deliberately incomplete physical candidates.

For example, the six-zero diagnostic first reaches source ordinal 25 at step 3,242 with header gap 15 and logical registers `[1,0,1,1,0,1,0,0,0]`. This is not the clean scheduler seed. The seven-zero control experiment shows that changing the source layout also requires checking startup independently of shortening the scanner. Receipt: `receipts/startup_variants.json`.

Failure to find a seed in a bounded run is not a proof that no later seed exists. A parsed frame with gap below the symbolic runtime's required bound is merely a syntactic tape-format observation.

## Provisional ideas and outstanding obligations

The following are research hypotheses, not established reductions:

1. An AX grammar with every path's maximum zero run at most five, and every increment path's maximum zero run at most four, may permit the shorter scanner. These address bounds alone do not prove all physical contracts; history-sharing and temporary-marker paths must also be checked.
2. A different allocation or grammar may supply a usable history-disambiguation helper without the extra reader. The one-row search does not settle this question.
3. A successfully recompiled source layout still needs an exact blank-start trace to a certified clean seed. The five-million-step experiments have not supplied it.
4. Only after all physical contracts, state counts, startup, and the inherited syntactic PA calibration are connected can a sub-194 consistency-equivalent TM be claimed. None of the supplied diagnostics completes those obligations.
