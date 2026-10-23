# Formal endpoints for the K-family candidates

**Current state (2026-10-22).** The exact [215-state machine](../candidate-k215/README.md)
has compiled correctness proofs in both Lean and Rocq. The original fresh Lean
build checked 204 project modules; [phase16](verification/k215/simplification/phase16/README.md)
retains the earlier checked quotient-unification snapshot.
Its zero-offset proposal is reconciled as
[Source 167](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-204.md). Rocq's
237 sources compile with closed endpoint assumption reports and recursive `coqchk`.
See the [215 verification record](verification/k215/README.md) for statements, evidence,
repairs, and reproduction commands. The internal PA endpoint remains open.

The [phase26 proof cleanup](verification/k215/simplification/phase26/README.md) removes **126 lines / 3,711 bytes**
from five files, sharing completeness, rank, satisfaction and tape proofs.
Kernel, actual-result, capture and archive checks pass for **230 providers
(56 fresh / 174 exact phase25 reuses)** and two fresh audits, with zero warnings.
The primary closure remains **172 modules / 1,720,244 source bytes**; its byte
saving overlaps the five-file measure. The machine remains 215 states, and the
internal PA endpoint remains open. [Previous checkpoint](verification/k215/simplification/phase25/README.md).

The [phase23 Lean checkpoint](verification/k215/simplification/phase23/README.md), independent actual readback,
evidence capture and independent capture review pass. Thirty-three maintained
sources remove **243 Lean lines / 13,016 bytes**; forty declarations retire and
three signatures become stronger. The check covers 230 providers (215 project
modules and fifteen existing clients): 199 fresh and 31 exact phase22 reuses,
plus two fresh endpoint audits. All selected providers and audits have zero
warnings. The primary endpoint falls from 179 to **172 project modules** and from
1,768,101 to **1,728,487 selected source bytes**; that import-closure measure
overlaps the maintained-file saving. The literal 215-state machine and endpoint
statements are unchanged; its internal PA endpoint remains open.

The [phase22 Lean check](verification/k215/simplification/phase22/README.md), independent actual readback, capture and independent capture review pass. Nine maintained sources remove **179 Lean lines / 10,782 bytes**,
including the attributed ConstructibleAbs normalization once. The check covers
226 providers: 56 fresh, 170 exact reuses, plus two fresh endpoint audits, all with
zero fresh warnings. The primary endpoint retains 179 modules and selects
1,768,101 source bytes. Machine and endpoint statements are unchanged.

The [phase21 Lean check](verification/k215/simplification/phase21/README.md) and both independent
reviews pass. One shared AX expression proof removes 1,085 Lean lines / 104,946
bytes; four retired writers bring active savings to 1,653 lines / 126,445 bytes.
The check covers 226 providers and two fresh endpoint audits, with zero fresh
warnings. The primary endpoint retains 179 modules and selects 1,771,267 bytes;
the large source savings include compatibility proofs. The 215-state machine
and its endpoint statements are unchanged.

The [phase20 Lean check](verification/k215/simplification/phase20/README.md)
passes for shared AX words and 55 transferred 219 macro contracts. It covers 227
providers and two fresh endpoint audits; all fresh checks have zero warnings.
Seven Lean modules are replaced and one common module is added, removing 3,059
Lean lines / 417,103 bytes. Retiring three obsolete writers gives net active
maintenance savings of 3,763 lines / 447,473 bytes. These savings include the
compatibility facades; the primary 215 endpoint grows to 179 modules /
1,768,653 source bytes. The machine and endpoint statements are unchanged.

The [phase19 Lean check](verification/k215/simplification/phase19/README.md)
passes for concise forwarding proofs and a shared iteration argument across five
roots. Seven Lean sources lose 169 lines / 6,449 bytes; including the synchronized
producer gives 167 lines / 6,241 bytes of maintenance savings. It checks 226
providers and two endpoint audits with exact retained profiles. The 178-module
endpoint selects 1,765,109 source bytes.

The [phase18 combined Lean check](verification/k215/simplification/phase18/README.md)
passes for shared 222/254 macro proofs and Claude Code's nine Profile/syntax and
RegisterPath simplifications. Across the same 199 selected project modules,
source size falls by 27,373 bytes / 683 Lean lines. The endpoint imports four
shared reference modules and grows from 174 to 178 modules. All retained profiles
match exactly; independent result review and evidence capture pass. The
[phase17 checkpoint](verification/k215/simplification/phase17/README.md) and
historical Rocq receipts retain their accepted scopes.

The supplemental reconciliations of
[Sources 168–174](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-205.md)
and [Source 175](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-207.md)
retain the delivered normalized-certificate, lookup, dependency and transport
proposals with their original status. The later phase-six checkpoint above
checks selected adaptations for the same K215 endpoint; the intake records do
not certify the other proposals or an alternate machine.

[Sources 176–178](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-208.md)
add affine/axiom transport, certificate and concrete-credit refinements, and
framed decoder evidence. Maintained Lean already has balanced certificate
storage. Phase six checks normalized source correspondence, stable-program
imports, fast transition lookup and the seed-model cleanup. Decoder factoring,
relative transports and concrete zero-credit integration retain their separate gaps.

Phase seven replaces the dominated-implication deduction development with two
pointwise lifts. Its 454-line source preserves the exact unrestricted numerical
row and all maintained callers; the unused distribution helper is removed.
The 187-module endpoint and a fresh five-client legacy audit pass. The remaining
proposals from batches 209–211 retain their separate pending reconciliation.

Phase eight factors the implication proof through a representation-independent
core and shares bundle semantics between both seed directions. Together these
proof sources shrink by 9,465 bytes. The exact 188-module endpoint and fresh
five-client legacy audit pass; selected adoption does not complete the incoming
report reconciliation.

Phase nine shares the positive Home return proof and its checked table gate, while
retaining all 6,176 branch outcomes. All nine site batches are freshly checked in
16.41 minutes (historical phase-six total: 27.49 minutes). The exact source-to-zipper
decoder prefix is checked separately; primitive factoring remains open. Both closed
endpoint clients and the original executor API controls pass.

Phase ten shortens the generic implication core by 4,639 bytes and 51 lines, with
the numeric adapter and all public types preserved. Eight affected modules and
both endpoint clients pass fresh checks; 189 providers retain exact phase-nine
bindings in the 197-module union.

Phase eleven adopts the [58-step derivation](verification/k215/simplification/phase11/README.md)
with two single-use aliases inlined. Removing the temporary seed wrapper saves
another 1,016 bytes and 43 lines in the core. The synchronized producer reproduces
the checked source; two unused templates are retired with their old bytes preserved.
Eight affected modules and both endpoint clients pass fresh checks, while 189
providers retain exact phase-ten bindings. All public types remain unchanged.

[Source 179](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-212.md)
reconciles the affine-core and CM215 continuation separately. Its ordinary source
review and submitted old-snapshot compiler receipts do not replace the maintained
Lean checkpoint.

Phase twelve splits the semantic interfaces from their older clients. The endpoint
closure falls from 192 to 179 modules, removing 233,503 bytes from its selected
sources. Fifteen affected modules and both endpoint clients pass fresh Lean checks;
169 providers retain exact phase-eleven bindings. A separate 67-module check with
two explicit clients preserves the old model/native interfaces. The seven edited
or new proof files grow by 491 bytes; no proof body or endpoint type changes.
[Sources 180–187](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-213.md)
reconcile the eight later reports separately from this selected adoption.

Phase thirteen realizes their shared-implication idea using the later upstream
58-step derivation. The core exports K, Peirce and S; the unrestricted calculus
uses the relation `True`, preserving its old interfaces and complete Tarski bridge.
The primary check has 36 fresh providers (33 project modules and three API clients)
and 151 phase-twelve reuses. A separate 68-module compatibility check with two
clients passes. Both unchanged endpoint audits retain their exact profiles and
zero warnings. The producer and ancestry input are synchronized; the supplied
research renderer is preserved as data and was not executed.

Phase fourteen shares derived-rule proofs through `Rows` instances for both named
calculi and makes the profile composition proofs use transitive containers directly.
The duplicated `KProfileTC` module and its generator are retired. The endpoint now
uses 178 project modules (2,093,112 bytes of selected sources); the primary and
compatibility checks cover 198 distinct project modules. The initial failure was
an audit-client binder omission, corrected without changing a production proof.

[Sources 188–192](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-214.md)
reconcile the later DenseBridge, PowerSets, direct-seed and quotient-sharing
proposals separately. Those proposals are not part of this phase-fourteen adoption;
their source censuses do not establish another checked endpoint.

Phase fifteen proves transfinite recursion once for a general relation and
specializes it to both existing hierarchies. The weak quotient shares only
hypothesis-free syntax with the strong lane and retains its weaker QHyp assumptions.
The PowerSets import cut preserves the full calibration through an explicit client;
Source193 supplies the shorter dense ending. The primary 194-provider and
compatibility 71-provider checks pass, binding 199 distinct project modules. The
endpoint selects 2,052,142 source bytes, 40,970 fewer than phase14. Two failed primary
attempts and their narrow import/client repairs remain excluded from acceptance.

[Sources 193–194](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-215.md)
reconcile exact residual contracts and shared scheduler proofs. Only the selected
dense ending enters this checkpoint; residual integration, subtree abbreviation
and scheduler sharing keep their separate proof and reproduction obligations.

Phase sixteen adopts a single `QHyp` quotient development and a CP/GIC adapter,
removing duplicated construction and axiom proofs. Twelve unused strong forwarding
helpers are removed and a one-use trace instance is inlined into the adapter.
The successful 195-provider primary and 78-provider compatibility checks bind 199
project modules, with the same 176-module endpoint and 2,028,295 selected source
bytes. Seventy API reports, ten endpoint reports, ten compatibility reports and
five WFTheory reports retain their exact checked profiles. All clients and endpoint
audits have zero warnings; all observed production warning messages already occur
in earlier logs. The original proposal is credited to Vladimir Reshetnikov and
Claude Opus 5.5 at `eb931b07ad8de83ba1a1d21dc84abe5a1c98364e`.

Phase seventeen combines the original-domain full seed proof, direct `C222`
enumerator compilers, computed decoder trees, AX words whose successors come from
the program, and further proof compression. It retains phase16's twelve unused
wrapper retirements and inline trace instance. Local cleanup removes another 18
Lean lines/690 bytes and 15 producer lines/488 bytes. The successful check covers
199 project modules and fourteen typed clients, plus two endpoint audits; all nine
215 site batches were checked fresh. Its scope does not include the full 217–225
endpoint stacks. Exact attribution and evidence status are on the
[phase17 page](verification/k215/simplification/phase17/README.md).

The [221](../candidate-k221/README.md) also has two closed endpoints for its exact table:

* **Rocq**: `K221F.CorrectDense221.tm221_halts_iff_ZFC_inconsistent`, which `coqchk`
  independently rechecked ([rocq/](rocq/README.md)); its calculus and program layer are in
  [rocq224/](rocq224/README.md);
* **Lean**: `KEndpoint221.blank_halts_iff_zfc_refutation : BlankHalts machine221 ↔ BProv ZFCax_s [] ⊥`,
  axioms `propext`, `Classical.choice`, `Quot.sound` ([below](#lean)).

The newer [219-state candidate](../candidate-k219/README.md) also has a closed **Lean** endpoint,
`KEndpoint219.blank_halts_iff_zfc_refutation` ([below](#the-219)); its Rocq and internal PA
endpoints remain open. The [217](../candidate-k217/README.md) proof sources remain
unchecked ([below](#the-217)). The 215's layers are described [below](#the-215).
The rest of this page records the earlier 225/224 plan, except the Lean section, which
describes the 221's endpoint.


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

The 221's Lean endpoint is closed:

```lean
KEndpoint221.blank_halts_iff_zfc_refutation :
  BlankHalts machine221 ↔ BProv ZFCax_s [] Form.fBot
```

`machine221` is the literal 442-row table of [zfc_k221.tm](../candidate-k221/zfc_k221.tm), and
`BlankHalts` is the blank-tape run of the repository's `Core` semantics (as for the 240). The
proof uses `propext`, `Classical.choice` and `Quot.sound` only. Where Elliot Glazer's Rocq
derives K's ZF interpretation syntactically, the Lean lower chain works with models.

| Layer | Statement | Modules |
| --- | --- | --- |
| **Dense bridge** | the literal `Machine 221` halts on the blank tape iff its K230-label table `tm221` does | [`KDenseBridge`](../../../Lean/BusyBeaver/ZFC/KDenseBridge.lean) (generic), [`KDense221`](../../../Lean/BusyBeaver/ZFC/KDense221.lean) (`commutes`: all 442 rows, one kernel check), [`KTable221`](../../../Lean/BusyBeaver/ZFC/KTable221.lean) |
| **Boot** | from the blank tape `tm221` reaches state 84 with the boot registers (`nextproof = 3`, `param1 = 3`) and 167 spare blocks after 409,835 steps | [`KBoot`](../../../Lean/BusyBeaver/ZFC/KBoot.lean), [`KFast221`](../../../Lean/BusyBeaver/ZFC/KFast221.lean) (balanced lookup tree), [`KBoot221`](../../../Lean/BusyBeaver/ZFC/KBoot221.lean) and 31 chunks of 2^14 steps |
| **Sites** | every one of the 4,744 decoder leaves of the 221's source passes the symbolic site check | [`KSim`](../../../Lean/BusyBeaver/ZFC/KSim.lean) (`checkEdge`, port of `Interpreter230Sites/Check`), [`KSites221`](../../../Lean/BusyBeaver/ZFC/KSites221.lean) and 9 batches (106 kernel blocks) |
| **Simulation** | the register program halts iff the machine does, from related configurations | [`KSim`](../../../Lean/BusyBeaver/ZFC/KSim.lean) (`halts_iff`, port of `Sim230`/`Sim230Main`), with K230's register lemmas ([`KTape`](../../../Lean/BusyBeaver/ZFC/KTape.lean): every table that agrees with K230 on the 44 rows they read and ends the increment K230's way or the 219's way) and the symbolic executor ([`KRuntimeCore`](../../../Lean/BusyBeaver/ZFC/KRuntimeCore.lean)) |
| **Source** | the 221's source halts from the boot registers iff `dag222` does iff `C222 F` | [`KSource221`](../../../Lean/BusyBeaver/ZFC/KSource221.lean) (WF tables, 2,247-entry offset certificate and mirror), [`Seed222`](../../../Lean/BusyBeaver/ZFC/Seed222.lean), [`L2Root222`](../../../Lean/BusyBeaver/ZFC/L2Root222.lean), [`Enum222`](../../../Lean/BusyBeaver/ZFC/Enum222.lean) |
| **Upper bound** | `C222 F → ZF ⊢ ⊥` | [`KUpper222`](../../../Lean/BusyBeaver/ZFC/KUpper222.lean) (the seed property holds in L by reflection) |
| **Lower chain** | `ZF ⊢ ⊥ → C222 F` | [`KEind222`](../../../Lean/BusyBeaver/ZFC/KEind222.lean) (`c222_complete`), [`KSeedDirect222`](../../../Lean/BusyBeaver/ZFC/KSeedDirect222.lean) (models of the derivable formulas have the seed property for every named relation, equality included, through a fresh-label bundle), [`KLowerSeed`](../../../Lean/BusyBeaver/ZFC/KLowerSeed.lean), [`KLowerRaw`](../../../Lean/BusyBeaver/ZFC/KLowerRaw.lean) (raw sets), [`KLowerRel`](../../../Lean/BusyBeaver/ZFC/KLowerRel.lean) / [`KLowerTag`](../../../Lean/BusyBeaver/ZFC/KLowerTag.lean) (the tagged domain `D_t`), [`KLowerEqv`](../../../Lean/BusyBeaver/ZFC/KLowerEqv.lean) / [`KLowerQHyp`](../../../Lean/BusyBeaver/ZFC/KLowerQHyp.lean) (coded bisimilarity; `D_t` satisfies [`KQHyp`](../../../Lean/BusyBeaver/ZFC/KQHyp.lean)), [`ProfileComposition`](../../../Lean/BusyBeaver/ZFC/ProfileComposition.lean) (shared contracts under transitive containers) and `KQ1*` (the bisimulation quotient on that interface; the CP/GIC quotient modules `Quotient*` instantiate it through `QuotientModel.ofCPGIC`), [`KQ1ZF`](../../../Lean/BusyBeaver/ZFC/KQ1ZF.lean) (ZF in the well-founded part) |
| **Endpoint** | the composition, and ZF ↔ ZFC refutation | [`KEndpoint`](../../../Lean/BusyBeaver/ZFC/KEndpoint.lean) (generic: the lower chain `c222_of_zf_refutation` and the composition, once for every K machine), [`KEndpoint221`](../../../Lean/BusyBeaver/ZFC/KEndpoint221.lean) (the 221's five inputs) |

The generators are in this directory: `generate_tables_lean.py`, `generate_dense221_lean.py`,
`generate_boot221_lean.py`, `generate_sites221_lean.py`, and `generate_source221_lean.py`.
Phase16 retires `generate_kq1.py`; its shared quotient proofs are maintained directly.
The three `dag222` macro modules, `L2Lib222`, `L2Macros222` and `L2Control222`,
are also maintained directly. Their common subroutine contracts reuse the native
254 proofs through `RMTransfer` and a kernel-checked closed set of unchanged nodes;
the rotated next-candidate loop and its fetch proof remain local. The former
`generate_l2k222.py` textual fork producer is retired. Earlier verification packets
retain their original producer snapshots and hashes as historical evidence.
Generated machine data is untrusted; the kernel re-checks it. The certificate decoder of `RMOffsetBisim` reads paths of up to 511 bits,
since the AX chain of `dag222` makes decoder paths 180 bits deep (`RMBisim.decode` stops at 127).

Compile times on this machine: `KSource221` about 60 minutes, the boot chunks about 20 seconds
each, the site batches about 3 minutes each; everything else is seconds.

### The 219

The [219](../candidate-k219/README.md) (Source 140) keeps the calculus, so the upper bound and the
semantic lower chain are reused as they are. Its endpoint
`KEndpoint219.blank_halts_iff_zfc_refutation : BlankHalts machine219 ↔ BProv ZFCax_s [] ⊥` adds:

- **Program**: [`Dag219`](../../../Lean/BusyBeaver/ZFC/Dag219.lean) is `dag222` with the equality test (node 123) replaced
  by Source 140's routine on nodes 461–466 ([`make_dag219.py`](make_dag219.py)).
  [`Dag219Equiv`](../../../Lean/BusyBeaver/ZFC/Dag219Equiv.lean) proves `IterHalts dag219 R ↔ IterHalts dag222 R` for
  every register file: both routines return normally iff `s1 = p2`, otherwise break one level,
  and clear both (proved once on raw registers); every other node below 461 is shared, so runs
  transfer by induction (`run_transfer`). With `L2K.dag222_seed_iff` this is `Dag219.seed_iff`;
  no L2 lemma is reproved. The `L2Lib219` … `L2Root219` source contracts cited by
  [k217-protected-tail-seed](../k217-protected-tail-seed/README.md) now share the state and
  macro proofs of `L2K`, transferring runs through `Dag219Bisim`. The obsolete
  [textual fork](verification/k215/simplification/phase20/retired/generate_l2q219.py) and
  [per-node AX writer](verification/k215/simplification/phase20/retired/generate_l2axioms222.py)
  are retired with their original bytes preserved.
- **Source**: [`KSource219`](../../../Lean/BusyBeaver/ZFC/KSource219.lean) relates the 219's 4,744-leaf source to
  `dag219` (2,237 certificate entries, none offset); it imports the program data only.
- **Engine**: the table in K230 labels ([`lean219/`](lean219/), new states renamed into freed
  labels) changes two engine rows, the read-0 rows of 113 and 198. `KTape` reads neither through
  the shared hypothesis: the increment's last steps are the disjunction `IncTail` (K230's return
  through 198 and 113, or the 219's bypass `198/0 → 1 L 40`).
- **Boot, sites, bridge**: the 312,617-step startup ([`KBoot219`](../../../Lean/BusyBeaver/ZFC/KBoot219.lean), 24 blocks),
  all 4,744 decoder leaves ([`KSites219`](../../../Lean/BusyBeaver/ZFC/KSites219.lean)), and the literal
  [`Machine 219`](../../../Lean/BusyBeaver/ZFC/KDense219.lean); composed in [`KEndpoint219`](../../../Lean/BusyBeaver/ZFC/KEndpoint219.lean).

### The 217

**Status: written, not yet kernel-checked.** The sources below have not been compiled; they are to
be built on a machine with more memory. Until both builds pass, these are unchecked proof
scripts, not theorems.

The [217](../candidate-k217/README.md) (Source 152) runs Source 149's dominated program, so three
layers are new; everything else is generated as for the 218 ([`prepare_k217.py`](prepare_k217.py),
data in [`lean217/`](lean217/)).

- **Calculus**: `CDom` restricts rho8 to `u ≤ a` ([`KCodeDom`](../../../Lean/BusyBeaver/ZFC/KCodeDom.lean)). It derives exactly
  `C222`'s codes: [`DomRho8`](../../../Lean/BusyBeaver/ZFC/DomRho8.lean) derives the unrestricted row through the
  representation-independent core [`DominatedImplication`](../../../Lean/BusyBeaver/ZFC/DominatedImplication.lean)
  ([`generate_dominated_implication_lean.py`](generate_dominated_implication_lean.py)). The separate
  [rho8cd derivation](rho8cd/PROVEIT_STATUS.md) now supplies the shorter generic Lean core;
  the [phase-eleven K215 check](verification/k215/simplification/phase11/README.md) preserves all public interfaces.
  The checked Rocq sources are retained.
  The replay of Source 149's 3,728-node certificate
  ([`generate_domrho8_lean.py`](generate_domrho8_lean.py)) is history.
- **Enumerator**: [`EnumDom`](../../../Lean/BusyBeaver/ZFC/EnumDom.lean) is `Enum222` with the AX fields `z, y, x` read as
  `U = d + z`, `A = U + x`, `B = h + y` (GEN at `U`, rho8 at `(A, B, c, U)`); soundness is unchanged
  and the compiler builds `CDom` derivations, the rho8 leaf being `AX(c, u, b, a - u)`. As for the
  215, `EnumDom.halts_iff` holds from every state between candidates with derivable registers, so
  [`SeedDom`](../../../Lean/BusyBeaver/ZFC/SeedDom.lean) is its instance at the seed.
- **Program**: [`DagDom`](../../../Lean/BusyBeaver/ZFC/DagDom.lean) is `dag219` with the AX word's prefix replaced
  ([`make_dagdom.py`](make_dagdom.py)). Only the root, the reads and the dispatch (13 nodes) reach the
  AX routine, so every other `L2K` lemma transfers by [`RMTransfer`](../../../Lean/BusyBeaver/ZFC/RMTransfer.lean)
  ([`L2Dom`](../../../Lean/BusyBeaver/ZFC/L2Dom.lean)); the AX routine shares the checked word
  evaluator ([`L2AxiomsDom`](../../../Lean/BusyBeaver/ZFC/L2AxiomsDom.lean)), and the root step
  is adapted from `L2Root222` ([`L2RootDom`](../../../Lean/BusyBeaver/ZFC/L2RootDom.lean)).
  The [former combined AX template](verification/k215/simplification/phase20/retired/generate_l2axiomsdom.py)
  is retired with its original bytes preserved.
- **Machine**: the source relates to `dagDom` by 2,239 certificate entries, none offset
  ([`KSource217`](../../../Lean/BusyBeaver/ZFC/KSource217.lean)); the 312,617-step startup ([`KBoot217`](../../../Lean/BusyBeaver/ZFC/KBoot217.lean)),
  all 4,751 decoder leaves ([`KSites217`](../../../Lean/BusyBeaver/ZFC/KSites217.lean); the source's paths reach 45 bits, so
  `KSim`'s path bound is now 48), the engine rows (`KTape` with the 219's increment bypass) and the
  literal [`Machine 217`](../../../Lean/BusyBeaver/ZFC/KDense217.lean), composed in [`KEndpoint217`](../../../Lean/BusyBeaver/ZFC/KEndpoint217.lean).

Rocq: variant `K217F` of [`rocq/rocq-extension`](rocq/rocq-extension/README.md) (`regenerate217.py`;
`rocqdom/DomRho8.v` is an adapter of the shared implication core `rocq224/src/DominatedCore.v`,
which also gives `CD222`), with the same three new layers and K230's runtime forked with paths
of up to 48 bits.

### The 215

**Lean and Rocq checked.** All 204 Lean project modules and both typed endpoint
clients pass, with axioms `propext`, `Classical.choice`, and `Quot.sound` only.
All 237 Rocq sources compiled, both sparse and dense endpoint files printed two
closed assumption reports, and the matching `coqchk` recursively rechecked the dense endpoint. The
[verification page](verification/k215/README.md) records the exact artifact, toolchains,
evidence and serial reproduction commands.

The [215](../candidate-k215/README.md) applies Source 159's command permutation to the 217's
program ([`prepare_k215.py`](prepare_k215.py), data in [`lean215/`](lean215/)); its calculus is the
217's.

- **Enumerator**: [`EnumPerm`](../../../Lean/BusyBeaver/ZFC/EnumPerm.lean): NIP at selector 0, DROP at 1, MP at 2 (reading
  its own field), AX at `3 + c` (fields `y, x`; `U = d`). The compiler sets the counter with
  `J u = MP u` from a cleared state; a dominated rho8 leaf is `J u; AX(c; a - u, b)`.
  [`SeedPerm`](../../../Lean/BusyBeaver/ZFC/SeedPerm.lean): completeness from the boot seed (candidate 4), using
  `START_Y = AX(0; 1, Y)` with `Y = 4`.
- **Program**: [`DagPerm`](../../../Lean/BusyBeaver/ZFC/DagPerm.lean) is `dagDom` with the root reading only the selector,
  MP reading its field (node 484), the AX word's read of `x` moved after its first `I`, and the
  permuted dispatch ([`make_dagperm.py`](make_dagperm.py)); the candidate's source relates to it by
  1,426 normalized certificate entries, preserving the 512-step decoder.
  The earlier phase-five ordinary certificate had 2,240 entries.
  [`KSource215Program`](../../../Lean/BusyBeaver/ZFC/KSource215Program.lean) holds the stable
  literal program/tree; [`KSource215Data`](../../../Lean/BusyBeaver/ZFC/KSource215Data.lean)
  supplies the relation to 16 independent kernel checks and the unchanged public
  [`KSource215`](../../../Lean/BusyBeaver/ZFC/KSource215.lean) composition theorem. [`L2Perm`](../../../Lean/BusyBeaver/ZFC/L2Perm.lean) transfers the `L2K` lemmas,
  [`L2AxiomsPerm`](../../../Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean) is the regenerated AX word and
  [`L2RootPerm`](../../../Lean/BusyBeaver/ZFC/L2RootPerm.lean) the re-proved dispatch and root step.
- **Machine**: the 95,714-step startup to the root with `nextproof = 4`, 65 zero cells before the
  register header and 40 spare blocks ([`KBoot215`](../../../Lean/BusyBeaver/ZFC/KBoot215.lean), 13 blocks; `KEndpoint` now
  takes the boot registers as a parameter), all 4,751 decoder leaves (paths up to 47 bits)
  ([`KSites215`](../../../Lean/BusyBeaver/ZFC/KSites215.lean)), the 219's engine rows, and the literal
  [`Machine 215`](../../../Lean/BusyBeaver/ZFC/KDense215.lean), composed in [`KEndpoint215`](../../../Lean/BusyBeaver/ZFC/KEndpoint215.lean).

Rocq: variant `K215F` (`regenerate215.py`): the 217's calculus files, the hand-written enumerator,
compiler, seed and dispatch in [`rocqperm/`](rocqperm/), `R0p` (the 215's boot registers) in
`Regs215.v`, and K230's runtime forked with the 215's startup frame and paths of up to 48 bits.

**Shared changes that need rebuilding everywhere**: `KSim`'s site-path bound is now 48 (was 40),
`KTape` takes row-level agreement plus the increment tail (`IncTail`), `KEndpoint` is generic in the
boot registers, and the 219/218 sources (`KSource219`, `KSource218`) import only the program data.
Every `KSites…Batch…` module and every `KEndpoint…` must be rebuilt against them, including the
221's, 219's and 218's.

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
