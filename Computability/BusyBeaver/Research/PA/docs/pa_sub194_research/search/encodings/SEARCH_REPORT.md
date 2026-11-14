# Bounded state-encoding searches on eight 194-state machines

## Result

No smaller machine was found. Twenty-four complete finite searches tested **1,195,148,640 patch trials**, with no surviving patch. These are eight input machines times three representation templates. The count is not a number of distinct machines, and the unsuccessful searches do not establish a lower bound on arbitrary machines.

Each search uses a radius-six tape window (thirteen cells), and requires a proposed child block to match one parent transition in **1 through 128 child transitions**, without reading outside that window. The dropped control cannot be the initial control. Its incoming transitions from other controls must all move in the same direction. One row of a retained control is synthesized; the other row is inherited, subject to the stated incoming-edge transformation.

| Input | Universal source outcomes checked | Source windows | Coarse windows | Exact blank startup | Patch trials per template |
|---|---:|---:|---:|---:|---:|
| Primary PA194 | 4,780 | 160,990 | 267,827 | 58,154 | 50,022,512 |
| PA194DHS | 4,752 | 163,775 | 274,589 | 58,014 | 49,123,904 |
| PA194QN | 4,755 | 161,714 | 267,227 | 58,154 | 50,022,512 |
| PA194H6 | 4,876 | 161,158 | 272,095 | 58,088 | 49,722,976 |
| PA194HA | 4,750 | 160,730 | 266,931 | 58,122 | 50,022,512 |
| PA194HAZ | 4,751 | 162,682 | 269,123 | 58,122 | 50,022,512 |
| PA194SUMS | 4,776 | 160,928 | 270,059 | 58,004 | 49,722,976 |
| Current PA194NS, sum guard | 4,751 | 160,711 | 268,843 | 58,004 | 49,722,976 |
| **Total per template** | | | | | **398,382,880** |

An earlier radius-four DHS screen tested 49,123,904 patches under each of the first two templates, also with no survivor. Those 98,247,808 trials are separate from the radius-six total above.

## Three precise templates

Let `a` be the dropped control, `b` the retained control, and `d` the common incoming direction, written as -1 or +1. Every parent configuration at a control other than `a` retains its tape and head position. Control `a` is represented by `b` with one of these changes:

1. **Head offset:** change head `h` to `h-2d`. Every surviving incoming transition into `a` reverses direction and targets `b`.
2. **Neighboring bit:** complement tape cell `h-d`. Every surviving incoming transition into `a` complements its written bit and targets `b`.
3. **Both changes together:** change head to `h-2d` and complement cell `h-d`. Every surviving incoming transition into `a` complements its written bit, reverses direction, and targets `b`.

The first two templates adapt the supplied `pa_consistency_comparison_2026_11_13/physical_search/fold_shift.cpp` and `fold_bitphase.cpp`, whose recorded input was PA196. The third composes their configuration encodings and is implemented here as `fold_combined.cpp`.

For each original transition from either `a` or `b`, the checker computes the encoded parent successor and asks whether the proposed child reaches exactly that control, head coordinate, and complete window tape in a positive number of steps. For other surviving controls the transformed incoming rows implement the encoding algebraically. For example, under the combined template, an original action writing `w` at `x` and moving `d` into `a` is represented by writing `1-w` at `x` and moving `-d` into `b`: the encoded new head is `(x+d)-2d=x-d`, and the complemented predecessor cell is `(x+d)-d=x`.

A successful universal certificate would therefore support positive-step simulation. Since the initial control is not dropped, the initial blank configuration is represented unchanged. Positive block durations prevent a finite child halt from being hidden inside an infinite sequence of parent transitions. This is a sufficient proof route for a found candidate; no candidate passed here.

## Context derivation and trust boundary

`derive_contexts.py` uses the inherited symbolic runtime from the current NS/SUMS packet. It reconstructs every primitive contract directly from the supplied addressed source and instruction graph. Nine arbitrary natural registers, an arbitrary header-gap parameter, and an opaque arbitrary finite spare tail are represented by that runtime. Variable-length unary runs are conservatively expanded into all radius-six prefixes. Arithmetic-box controls and self-loop controls receive the entire coarse blank-window closure rather than sampled register values. The exact finite bootstrap is separately simulated to its complete clean source frame.

The resulting source windows are intersected with the coarse blank-window invariant. Intersecting two sound overapproximations is sound. Both the inherited symbolic arithmetic-box lemmas and the source/frame interpretation remain mathematical dependencies. The scripts do not independently reprove those box lemmas or produce a new Lean/Rocq endpoint. The negative results are exact exclusions only for the displayed finite input windows, templates, and step limit.

Positive and adverse toy controls were executed for every encoding. They accept a three-step implementation with the intended displacement/restoration and reject the designated witness after changing a helper direction or restoration bit. These controls check particular cases of the search programs; they are not a formal verification of the programs.

## Offline reproduction

The supplied `machines/` inputs, `machine_manifest.json`, and `reference/symbolic_runtime.py` suffice. No external checkout or network is needed for replay. Python 3.10+ and a C++17 compiler are required. In this directory:

```sh
g++ -O3 -std=c++17 fold_shift.cpp -o fold_shift
g++ -O3 -std=c++17 fold_bitphase.cpp -o fold_bitphase
g++ -O3 -std=c++17 fold_combined.cpp -o fold_combined
python3 check_controls.py
python3 run_batch.py
python3 run_combined.py
```

`run_batch.py` regenerates all source windows and runs the first two templates. `run_combined.py` consumes those windows and runs the third. The programs write fresh receipts beside the inputs. The original completed receipts are `batch_receipt.json`, `combined_receipt.json`, and the per-machine `*_r6/receipt.json`/output files. Execution time is not a verification criterion. Do not run Python with assertions disabled.

`prepare_machines.py --repo PATH --incoming PATH` can reconstruct the uniform inputs from the pinned ProveIt tree and the five extracted incoming packets. It is unnecessary for offline replay with the bundled inputs. Source attribution and licenses are preserved in `UPSTREAM_NOTICE.md`, `LICENSE.JamesChang`, and `LICENSE.ProveIt`.
