# Formal correctness of the exact 215-state machine

**Both proof lanes pass** (2026-10-21), for the same literal machine.

The original fresh full builds below were recorded at `613f9cf28a`.
[Phase16](simplification/phase16/README.md) retains the preceding accepted
quotient-unification snapshot and its exact source, profile and warning records.

The [phase19 Lean check](simplification/phase19/README.md) passes for 226
providers: 211 project modules and fifteen typed clients. Sixteen affected providers
compile fresh, 210 reuse exact source and dependency bindings, and both endpoint
audits compile fresh. All retained assumption profiles match exactly. Seven Lean
files lose 169 lines / 6,449 bytes; the 178-module endpoint selects 1,765,109 bytes.
The record preserves an initial baseline stop on two inherited linter warnings.

The [phase18 combined Lean check](simplification/phase18/README.md) passes for
214 providers: 199 project modules and fifteen typed clients, with 107 fresh
compilations and 107 exact-source reuses, plus two fresh endpoint audits. All nine
215 site batches were checked fresh. The endpoint selects 178 modules /
1,767,300 source bytes. All retained profiles match exactly; the new macro client
matches its ten-report baseline. Independent result review and evidence capture
pass. Accepted provider records contain 16 warning occurrences (9 fresh); the fresh warning headlines already appeared in the same modules. All fifteen typed clients and both endpoint audits have zero warnings.
The phase18 record preserves the initial certificate timeout, session interruption and optional
namespace-probe failure. Earlier accepted builds retain their historical scopes.

| System | Completed checks | Endpoint assumptions |
| --- | --- | --- |
| Lean 4.32.0 | 204 freshly compiled project modules and two typed endpoint clients | `propext`, `Classical.choice`, `Quot.sound` only |
| Rocq 9.1.0, rocq-stdlib 9.0.0 | 237 freshly compiled sources and recursive `coqchk` | Both sparse and dense theorem pairs are closed under the global context |

The [Lean record](lean/actual/final-review.json) and
[Rocq record](rocq/actual/actual-review.json) bind the actual sources, dependency
objects, compiler commands and raw logs. The raw
[Lean endpoint reports](lean/actual/audit/independent/compiler.log),
[Rocq endpoint reports](rocq/actual/K215F.CorrectDense215.log), and
[recursive checker log](rocq/actual/coqchk.log) are retained separately.

The target is the accepted [K215 machine](../../../candidate-k215/README.md):
215 working states, two symbols, one two-way infinite tape, blank input, initial
state 0, and a separate halt. Initialization is included in the state count.
Both proof lanes target this same dense table, rather than a same-size variant.

| Input | SHA-256 |
| --- | --- |
| [Dense transition table](../../../candidate-k215/k215.tm) | `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090` |
| [Native transition table](../../../candidate-k215/k215.native.tm) | `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2` |
| [Source](../../../candidate-k215/sites215.json) | `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba` |

The closed theorem checked in each system is

```text
Halt(K215, blank) ↔ ZFC has a finite derivation of falsity.
```

Its negation gives nonhalting iff syntactic consistency of ZFC. Neither theorem
takes consistency as a premise. These are external proof-assistant theorems;
this work does not supply an internal PA proof or a derivation encoded in ZFC's
own proof syntax.

Lean's [`KEndpoint215.blank_halts_iff_zfc_refutation`](../../../../../Lean/BusyBeaver/ZFC/KEndpoint215.lean)
and Rocq's [`tm215_halts_iff_ZFC_inconsistent`](../../rocq/rocq-extension/coq/215/CorrectDense215.v)
compose the same layers: dense-state renaming, blank initialization, binary/source
simulation, source/program correspondence, and proof enumeration with its ZFC
calibration. Lean instantiates the shared endpoint theorem; Rocq's dense proof
applies the state-renaming equivalence to its sparse
endpoint. The large literal tables and arithmetic certificates are kernel-checked
data, while these final compositions stay small.

The [Lean reproduction driver](lean/README.md), using Lean 4.32.0, selects 178
project modules from the current phase19 sources and then two explicit endpoint
clients. The original fresh build selected 204. The
[Rocq reproduction driver](rocq/README.md), using Rocq 9.1.0 and rocq-stdlib 9.0.0,
selects 237 sources: 195 from the pinned reference and 42 for K215. Both use the
same compiler lock and run one proof compiler at a time. Lean's shipped core and
Rocq's installed standard library are explicit toolchain boundaries.

The Lean endpoint clients have zero warnings; the original full build retained
34 project linter warnings, and the subsequent records list the remaining project linters. Rocq's global `coqchk -o` context lists three utility axioms
from imported libraries, detailed on its [evidence page](rocq/README.md). None occur
in the four endpoint dependency reports, which are closed.

The [independent audit](independent-audit/README.md) binds all 430 machine actions,
all 4,751 expanded source leaves, and the literal bootstrap. It also preserves
the original draft review, the bootstrap repair, the Lean certificate partition
and their historical receipts. Those source/data checks remain distinct from
the final kernel checks. Root's separate read-only reviews of the
[Lean bindings](root-lean-review/actual.json) and
[Rocq bindings and packaged records](root-rocq-review/actual.json) also pass.

Attribution for the machine and inherited mathematics is retained in
[K215's notice](../../../candidate-k215/NOTICE.md). The Lean build and repairs are
by `opening_encoder`, the Rocq build and repairs by `review_upstream_reflection`,
the independent reviews by `drop_contract`, and integration by root.
