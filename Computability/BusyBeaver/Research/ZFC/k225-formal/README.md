# Formal endpoints for the K-family candidates

**Current state (2026-10-20).** The [221](../candidate-k221/README.md) has a
closed Rocq endpoint, `K221F.CorrectDense221.tm221_halts_iff_ZFC_inconsistent`, which `coqchk`
independently rechecked ([rocq/](rocq/README.md)). Its calculus and program layer are in
[rocq224/](rocq224/README.md). The Lean endpoint is in progress (layers below). The rest of this
page records the earlier 225/224 plan. The newer [219-state candidate](../candidate-k219/README.md)
has an ordinary simulation/calibration argument; its exact-table Lean and internal PA
endpoints remain open.


The [224](../candidate-k224/README.md) (Source 125) supersedes the 225 as the smallest
candidate, so it is the target. The 225's endpoints are built first, because everything they
need carries over except the 224's new logic; see [Retargeting to the 224](#retargeting-to-the-224).

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
| **B. Machine** | blank halting of the 225 ↔ `Halts p225` from the startup registers `(3,0,0,0,3,0,0,0,0)` | port Elliot's TM side (`Runtime230Core`, `Tape230Blocks`, `Tape230Carry`, `Interpreter230Sites/Check`, `Sim230`, `Boot230`; about 2,800 hand-written lines). It checks every leaf by computation over the program tree, so it is table-parametric, unlike the 561 generated coverage modules of the 240 | **in progress.** Done: [`KZip`](../../../Lean/BusyBeaver/ZFC/KZip.lean) (trimmed list zippers, the counterpart of `Zip`/`TM230`); [`KRuntimeCore`](../../../Lean/BusyBeaver/ZFC/KRuntimeCore.lean) (the run-length symbolic executor, `exec_sound`, `sMatches_conc`); [`KTableCore`](../../../Lean/BusyBeaver/ZFC/KTableCore.lean) and the generated [`KTable230`](../../../Lean/BusyBeaver/ZFC/KTable230.lean)/[`KTable225`](../../../Lean/BusyBeaver/ZFC/KTable225.lean) ([`generate_tables_lean.py`](generate_tables_lean.py)); [`KTape`](../../../Lean/BusyBeaver/ZFC/KTape.lean) (`boxLemmas`: the four register routines, proved once for every table that agrees with K230 on the 23 engine states they read); [`KEngine225`](../../../Lean/BusyBeaver/ZFC/KEngine225.lean) (the 225 agrees, by `decide`) and [`KEngine224`](../../../Lean/BusyBeaver/ZFC/KEngine224.lean) (so does the 224). Next: the site checks, `Sim230`, `Boot230` |
| **C1. Program → K** | `Halts p230` from the seed ↔ the K numerical calculus derives falsity | port Elliot's `coq/logic` (14 files, about 1,500 lines) and the program-to-enumerator part of `coq/prog`; reuse ProveIt's `Code254`, `Enum254` and `L2*` ports where K230 keeps Jeff's structure | to do |
| **C2. K ↔ ZFC** | K's calculus proves falsity ↔ StandardZFC proves falsity | port Elliot's `coq/settheory` (61 files, about 6,100 lines: `KPrime*`, `KDecode*`, `KQuot*`, `KUpper*`); reuse ProveIt's ports of Jeff's quotient, well-founded and Choice calibration (`Quotient*`, `WFTheory`, `ChoiceCalibration254`, `ConstructibleChoice`) | to do |

The Lean endpoint composes A, B, C1 and C2. Layers B, C1 and C2 are independent ports and can
proceed in parallel. Each needs the exact upstream statements it consumes pinned to
`3142e4d`, and each should keep Elliot's file structure, so that the correspondence stays
auditable.

Build rule on this machine: one Lean module per `lake` invocation, one build at a time machine
wide (see the BusyBeaver build notes).

## Retargeting to the 224

The 224 keeps the K-family engine and changes the source. Its source enumerates the theorems
of a calculus **K′**, not K. K′ cancels four double-negation pairs in K's formula and bundle,
and it replaces equality vacuity by the canonical helper
`Eq(a,b) → All(RelCode(a,b), Eq(a,b))` with `RelCode(a,b) = 4·P(a,b) + 1`. Then three
rotations and the fold 191 → 157 save the state. The package
(`portable/theory/` of Source 125) argues every step on paper.

| Piece | For the 224 |
| --- | --- |
| TM side: runtime, register lemmas, interpreter, simulation, boot (Rocq forks; Lean layer B) | **carries over.** The checks run by computation on the literal table. The 224 agrees with K230 on the register states (`KEngine224`), and its startup is the same 409,835 steps. The Rocq forks are regenerated with K labels 79, 140, 175, 191, 208 and 229 disabled. |
| Source: p224 against a program for K′ | **new.** p224 is not bisimilar to K230's source, since it emits different formulas. It is to be related to a K′ enumerator: the emitter contract, the fusion certificate (1,563 nodes) and eleven local register-program bisimulations ([`enumerator_adaptation.md`](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/125-k224-portable-theory-enumerator_adaptation.md)). |
| Program → calculus | **adapted.** Elliot's `Enum230`/`L1_Comp230` interfaces with the gated bundle replaced, as in the note above. |
| K′ ⊢ ⊥ ⇒ K ⊢ ⊥ | **new, easy.** The fused formulas are classically equivalent to K's, and the helper is an instance of K's vacuity. |
| K ⊢ ⊥ ⇒ K′ ⊢ ⊥ | **new, the main work.** The equality-indiscernibility argument: Source 116's restricted-helper bootstrap plus a K-specific matrix/binder coupling ([`k_equality_helper_extension.md`](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/125-k224-portable-theory-k_equality_helper_extension.md); certificate: 68 closed roots, 59,947 nodes). |
| K ↔ ZFC | **unchanged.** Elliot's `settheory` in Rocq; layer C2 in Lean. |

Order of work: finish Lean layer B, which serves both tables. In Rocq, add the 224's K′
calibration on top of Elliot's development and an adapted enumerator. Then compose with the
regenerated TM side, as the 225 extension does.
