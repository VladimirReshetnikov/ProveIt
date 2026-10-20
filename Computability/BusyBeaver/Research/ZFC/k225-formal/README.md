# Formal endpoints for the 225-state candidate

Target: for the exact table of [candidate-k225](../candidate-k225/README.md) (canonical SHA-256
`f5d69a16…`), prove

  the machine halts from the blank tape ↔ StandardZFC ⊢ ⊥

in **Rocq** and in **Lean**.

## Rocq

The route reuses Elliot Glazer's [k230-rocq](https://github.com/elliotglazer/k230-rocq)
(`3142e4d`, Rocq 9.1.0 with rocq-stdlib 9.0.0). It extends Source 123's K226F extension, which
proves the same statement for its own 226. The new pieces are:

- the 225's inputs:
  - the sparse table in K230 labels, with labels 79, 140, 175, 208 and 229 disabled;
  - the dense table, which is byte for byte the public canonical table;
  - the 5,121-leaf source;
- an offset-bisimulation certificate between the 225's source and K230's, from
  [`gen_cert.py`](gen_cert.py). It has 2,377 entries, 8 of them with register 5 offset by one.
  The generator reproduces Source 123's 2,376-entry certificate for its 226 byte for byte;
- `regenerate225.py`, adapted from Source 123's generator. It writes the 19 `K225F` sources:
  the runtime forks of the K230 runtime, `Source225`, `Dense225`, `Correct225` and
  `CorrectDense225`.

Endpoint: `K225F.CorrectDense225.tm225_halts_iff_ZFC_inconsistent`. **Status:
`PASS_CLOSED_KERNEL`.** All 19 files compile closed, and `coqchk` independently rechecked the
target (1,093 s). The buildable extension, the receipts and the toolchain notes are in
[`rocq/`](rocq/README.md).

## Lean

The statement reaches StandardZFC through K. ProveIt's Lean already has ports of Jeff's ZF/ZFC
chain (Tarski completeness, quotient models, the Choice and Foundation calibration) and of the
register-program machinery. Elliot's K-specific Rocq development has no Lean counterpart yet. The
work splits into three layers.

| Layer | Statement | Route | Status |
| --- | --- | --- | --- |
| **A. Source** | `Halts p225 ⟨[], R⟩ ↔ Halts p230 ⟨[], R⟩` for every register file | [`RMOffsetBisim`](../../../Lean/BusyBeaver/ZFC/RMOffsetBisim.lean) (an offset extension of `RMBisim`) plus the generated [`KSource225`](../../../Lean/BusyBeaver/ZFC/KSource225.lean): the certificate and its mirror, kernel-checked in 16 chunks each | **done**: `KSource225.p225_halts_iff`, axioms `propext` and `Quot.sound` only ([audit](../../../Lean/BusyBeaver/ZFC/KSource225Audit.lean)); the module compiles in about 15 minutes |
| **B. Machine** | blank halting of the 225 ↔ `Halts p225` from the startup registers `(3,0,0,0,3,0,0,0,0)` | port Elliot's TM side (`Runtime230Core`, `Tape230Blocks`, `Tape230Carry`, `Interpreter230Sites/Check`, `Sim230`, `Boot230`; about 2,800 hand-written lines). It checks every leaf by computation over the program tree, so it is table-parametric, unlike the 561 generated coverage modules of the 240 | **in progress.** Done: [`KZip`](../../../Lean/BusyBeaver/ZFC/KZip.lean) (trimmed list zippers, the counterpart of `Zip`/`TM230`); [`KRuntimeCore`](../../../Lean/BusyBeaver/ZFC/KRuntimeCore.lean) (the run-length symbolic executor, `exec_sound`, `sMatches_conc`); [`KTableCore`](../../../Lean/BusyBeaver/ZFC/KTableCore.lean) and the generated [`KTable230`](../../../Lean/BusyBeaver/ZFC/KTable230.lean)/[`KTable225`](../../../Lean/BusyBeaver/ZFC/KTable225.lean) ([`generate_tables_lean.py`](generate_tables_lean.py)); [`KTape`](../../../Lean/BusyBeaver/ZFC/KTape.lean) (`boxLemmas`: the four register routines, proved once for every table that agrees with K230 on the 23 engine states they read); [`KEngine225`](../../../Lean/BusyBeaver/ZFC/KEngine225.lean) (the 225 agrees, by `decide`). Next: the site checks, `Sim230`, `Boot230` |
| **C1. Program → K** | `Halts p230` from the seed ↔ the K numerical calculus derives falsity | port Elliot's `coq/logic` (14 files, about 1,500 lines) and the program-to-enumerator part of `coq/prog`; reuse ProveIt's `Code254`, `Enum254` and `L2*` ports where K230 keeps Jeff's structure | to do |
| **C2. K ↔ ZFC** | K's calculus proves falsity ↔ StandardZFC proves falsity | port Elliot's `coq/settheory` (61 files, about 6,100 lines: `KPrime*`, `KDecode*`, `KQuot*`, `KUpper*`); reuse ProveIt's ports of Jeff's quotient, well-founded and Choice calibration (`Quotient*`, `WFTheory`, `ChoiceCalibration254`, `ConstructibleChoice`) | to do |

The Lean endpoint composes A, B, C1 and C2. Layers B, C1 and C2 are independent ports and can
proceed in parallel. Each needs the exact upstream statements it consumes pinned to
`3142e4d`, and each should keep Elliot's file structure, so that the correspondence stays
auditable.

Build rule on this machine: one Lean module per `lake` invocation, one build at a time machine
wide (see the BusyBeaver build notes).
