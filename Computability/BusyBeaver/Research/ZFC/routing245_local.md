# Register operations on the exact routing245 machine

Three Lean modules establish local execution contracts for the literal
245-state table:

| Module | Contract | Theorem probes / callers |
| --- | --- | --- |
| [Routing245Pulse](../../Lean/BusyBeaver/ZFC/Routing245Pulse.lean) | Both three-step contextual pulse identities and whole-tape transport. | 3 / 4 |
| [RegisterMarkRouting245](../../Lean/BusyBeaver/ZFC/RegisterMarkRouting245.lean) | Nine selectors and marking with arbitrary values, contexts and terminal words. | 10 / 6 |
| [Routing245Boxes](../../Lean/BusyBeaver/ZFC/Routing245Boxes.lean) | Complete increment and both decrement excursions, including the spare suffix. | 14 / 19 |

All 27 theorem probes and 29 callers pass with zero warnings in the selected
runs. The proofs quantify over arbitrary natural register values and finite
contexts. `ZipRep` conclusions account for the entire tape, including its zero
exterior. They use the already checked routing245 transition rows and generic
list/scanner lemmas from the earlier constructions.

Marking takes exactly `2 * width pre + 3` transitions. Increment takes
`2 * width file + 7`, increases the selected register, and appends one
value-one spare. Positive decrement takes `2 * width pre + 4`, reduces the
selected value and moves the file boundary right by one cell. Zero decrement
takes `2 * width pre + 7` and restores the file; its contract explicitly
requires a following block. A file with nine primary registers and at least
one spare supplies that premise for every primary selection.

The selected actual records are
[Pulse](results/routing245-pulse-verification.json),
[Mark](results/routing245-mark-verification.json), and
[Boxes](results/routing245-boxes-verification.json). Their source/audit times
are respectively 0.653/0.656, 1.138/0.498, and 1.674/0.608 seconds. Pulse uses
four project providers, Mark seven, and Boxes eight, each with the toolchain's
`Init` and `Omega`. Each source/audit pair shares 120 seconds, uses
`-j1 -M4096` and default proof limits, and records the fresh object before its
audit. No dependency rebuild, download or compiler-version query is used.

The first Boxes run also passed, with seven unused-simplifier-argument
warnings. Removing exactly those seven arguments produced the selected clean
run; theorem statements and the audit stayed unchanged. Both runs and their
exact sources are retained in the [history](routing245-local/history.json).
The [publication manifest](routing245-local/publication.json) binds the three
maintained modules, audits, raw records, logs and provenance. Original guards
retain their historical paths and cached-object prerequisites.

These are local arithmetic and marking proofs. The symbolic executor, all
8,391 instruction cases, complete runtime relation and 407,915-step blank
initialization still require their own checked composition. The
[source-program equivalence](bisim_routing245.md) is already complete; the
245-state binary consistency endpoint and PA internalization remain open.
Original-machine, framework and submission attribution is retained in the
source headers and [candidate documentation](candidate-routing245/README.md).
