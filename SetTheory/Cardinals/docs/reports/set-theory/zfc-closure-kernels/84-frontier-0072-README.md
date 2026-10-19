# Atomic membership target: a proved semantic idea and a negative price control

This directory is self-contained. Run with Python 3.10 or later:

```sh
python atomic_target_experiment.py
```

There are no third-party Python dependencies. The script reads the pinned
source DAG, invokes the included unchanged public Wade backend, reextracts the
live decision edges, and independently interprets the exact register-path
semantics. It writes two complete transition tables and
`atomic-target-evidence.json` in this directory.

The experiment changes the NIP acceptance target from cached code `H == 1`
to `H % 4 == 1`. Every code in that residue class is a membership atom. The
ordinary proof in `atomic-target-note.tex` shows, inside ZFC, that derivability
of any such atom implies derivability of the original falsity code. Thus the
broader target is semantically sound. The note also proves the concrete
six-node destructive test and the command-level halting transfer.

The exact raw compiler cost is unfavorable:

| Program | Decision states | Framework states | Working states |
|---|---:|---:|---:|
| Published source | 219 | 62 | 281 |
| Atomic target | 223 | 62 | 285 |

The complete NIP test checks 16,384 executions: both implementations, cache
values 0 through 127, and stack values 0 through 63. It checks every continuing
output register, not just the halt flag. The isolated macro additionally checks
1,024 cache values and the exact clock `6*(H//4) + [1,2,4,5][H%4]`.
Pure decoder results are memoized; the source dictionaries are immutable, and
the evaluator still performs every register instruction.

These finite checks are independent controls for the supplied universal
ordinary proof. They are not a kernel certificate. No theorem simulating the
new compiled binary table has been completed, and raw Wade pricing is not the
separately optimized 246-state interpreter's pricing. These are compiler
outputs for an experiment, not a verified machine below 246 states.

## Provenance

Repository snapshot:

- [ProveIt commit 79957d7b290ec807d434959a0c6ecc06ee90b419](https://github.com/VladimirReshetnikov/ProveIt/tree/79957d7b290ec807d434959a0c6ecc06ee90b419)
- `inputs/recover_wade_dag.py` is copied unchanged from
  `Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py`.
- `inputs/Dag254.v` is copied unchanged from
  `lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v`.
- The four files in `wade_copy/` are copied unchanged from the repository's
  `lib/jeff-busy-beaver-zfc254/ZF/generator/` directory.
- The upstream files are pinned to
  [jeff87654/busy-beaver commit 297ab8df7e5de329605c3875b4934643b371a5e3](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3).

The public register-machine framework is Wade's work, the original source
program is Mira-Cult's work, and the upstream formal verification is Jeff's
work. License copies are included. The original DAG and backend sources are
not modified; the experiment constructs a new in-memory DAG. Each output
table's sole undefined backend row `(1.inc, 1)` is explicitly totalized as
write-1, move-right, halt, without adding a working state.

The proof note's API references are to
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`,
`Code254Models.lean`, `NativeTheory254.lean`, and `Enum254.lean` in the pinned
ProveIt snapshot.

## Additional target obstruction

`target-limits.md` explains why accepting code zero, or any nonempty downward-closed
numerical target, is unsound. Run `python seed_zero_control.py` to reproduce the
64-instruction literal-DAG trace reaching the first NIP with cache zero from
the 246 logical seed. Its output is `seed-zero-control.json`.
