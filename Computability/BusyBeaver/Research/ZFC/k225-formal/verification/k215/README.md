# Formal correctness of the exact 215-state machine

**Both proof lanes pass** (2026-10-21), for the same literal machine.

The original fresh full builds below were recorded at `613f9cf28a`.
[Phase16](simplification/phase16/README.md) retains the preceding accepted
quotient-unification snapshot and its exact source, profile and warning records.

The [phase27 proof cleanup](simplification/phase27/README.md) removes **118 lines / 4,635 bytes**
from five proof files. Its full Lean check passes for **230 providers and two
endpoint audits**, with zero warnings and exact retained profiles. The machine
remains **215 states**; its internal PA endpoint and minimum-state theorem remain open.

The [phase26 proof cleanup](simplification/phase26/README.md) removes **126 lines / 3,711 bytes**
from five files, sharing completeness, rank, satisfaction and tape proofs.
Kernel, actual-result, capture and archive checks pass for **230 providers
(56 fresh / 174 exact phase25 reuses)** and two fresh audits, with zero warnings.
The primary closure remains **172 modules / 1,720,244 source bytes**; its byte
saving overlaps the five-file measure. The machine remains 215 states, and the
internal PA endpoint remains open. [Previous checkpoint](simplification/phase25/README.md).

The [phase23 Lean checkpoint](simplification/phase23/README.md), independent actual readback,
evidence capture and independent capture review pass. Thirty-three maintained
sources remove **243 Lean lines / 13,016 bytes**; forty declarations retire and
three signatures become stronger. The check covers 230 providers (215 project
modules and fifteen existing clients): 199 fresh and 31 exact phase22 reuses,
plus two fresh endpoint audits. All selected providers and audits have zero
warnings. The primary endpoint falls from 179 to **172 project modules** and from
1,768,101 to **1,728,487 selected source bytes**; that import-closure measure
overlaps the maintained-file saving. The literal 215-state machine and endpoint
statements are unchanged; its internal PA endpoint remains open.

Fourteen existing typed clients are included in the 199 fresh providers. The
independent actual readback checks 146 current mandatory present inputs and
sixteen absences; all 93 client reports, five `WFTheory` reports and ten
endpoint-audit reports retain their exact profiles. It binds 218 raw provider
records; twelve inherited providers retain the accepted aggregate boundary for
missing original records. Phase22's historical thirty-one missing records remain
documented; no records are fabricated. The capture and independent capture review
pass for 928 blobs, 2,078 logical entries, 2,074 source aliases and 1,089 raw
evidence files.

The [phase22 Lean check](simplification/phase22/README.md), independent actual readback, capture and independent capture review pass. Nine maintained sources remove **179 Lean lines / 10,782 bytes**,
including the attributed ConstructibleAbs normalization once. The check covers
226 providers: 56 fresh, 170 exact reuses, plus two fresh endpoint audits, all with
zero fresh warnings. The primary endpoint retains 179 modules and selects
1,768,101 source bytes. Machine and endpoint statements are unchanged.

The [phase21 Lean check](simplification/phase21/README.md) and both independent
reviews pass. One shared AX expression proof removes 1,085 Lean lines / 104,946
bytes; four retired writers bring active savings to 1,653 lines / 126,445 bytes.
The check covers 226 providers and two fresh endpoint audits, with zero fresh
warnings. The primary endpoint retains 179 modules and selects 1,771,267 bytes;
the large source savings include compatibility proofs. The 215-state machine
and its endpoint statements are unchanged.

The [phase20 Lean check](simplification/phase20/README.md) passes for
227 providers: 212 project modules and fifteen unchanged typed clients. Fourteen
providers and both endpoint audits compile fresh with zero warnings; 213 providers
reuse exact accepted bindings. Shared AX words and 55 transferred 219 macro contracts
remove 3,059 Lean lines / 417,103 bytes across the selected sources. Three obsolete
writers are retired with their bytes preserved. The primary 215 endpoint selects
179 modules / 1,768,653 source bytes; its machine and theorem statements are unchanged.

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

The [Lean reproduction driver](lean/README.md), using Lean 4.32.0, selects 172
project modules from the current maintained sources and then two explicit endpoint
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
