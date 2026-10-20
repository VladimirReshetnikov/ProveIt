# Formal endpoints for the K-family candidates

**Current state (2026-10-20).** The [221](../candidate-k221/README.md) has two closed endpoints for
its exact table:

* **Rocq**: `K221F.CorrectDense221.tm221_halts_iff_ZFC_inconsistent`, which `coqchk`
  independently rechecked ([rocq/](rocq/README.md)); its calculus and program layer are in
  [rocq224/](rocq224/README.md);
* **Lean**: `KLower221.blank_halts_iff_zfc_refutation : BlankHalts machine221 ↔ BProv ZFCax_s [] ⊥`,
  axioms `propext`, `Classical.choice`, `Quot.sound` ([below](#lean)).

The newer [219-state candidate](../candidate-k219/README.md) also has a closed **Lean** endpoint,
`KLower219.blank_halts_iff_zfc_refutation` ([below](#the-219)); its Rocq and internal PA
endpoints remain open. The rest of this page records the earlier 225/224 plan, except the Lean section, which
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
KLower221.blank_halts_iff_zfc_refutation :
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
| **Simulation** | the register program halts iff the machine does, from related configurations | [`KSim`](../../../Lean/BusyBeaver/ZFC/KSim.lean) (`halts_iff`, port of `Sim230`/`Sim230Main`), with K230's register lemmas ([`KTape`](../../../Lean/BusyBeaver/ZFC/KTape.lean), [`KEngine221`](../../../Lean/BusyBeaver/ZFC/KEngine221.lean)) and the symbolic executor ([`KRuntimeCore`](../../../Lean/BusyBeaver/ZFC/KRuntimeCore.lean)) |
| **Source** | the 221's source halts from the boot registers iff `dag222` does iff `C222 F` | [`KSource221`](../../../Lean/BusyBeaver/ZFC/KSource221.lean) (WF tables, 2,247-entry offset certificate and mirror), [`Seed222`](../../../Lean/BusyBeaver/ZFC/Seed222.lean), [`L2Root222`](../../../Lean/BusyBeaver/ZFC/L2Root222.lean), [`Enum222`](../../../Lean/BusyBeaver/ZFC/Enum222.lean) |
| **Upper bound** | `C222 F → ZF ⊢ ⊥` | [`KUpper222`](../../../Lean/BusyBeaver/ZFC/KUpper222.lean) (the seed property holds in L by reflection) |
| **Lower chain** | `ZF ⊢ ⊥ → C222 F` | [`KEind222`](../../../Lean/BusyBeaver/ZFC/KEind222.lean) (`c222_complete`), [`KSeedModel222`](../../../Lean/BusyBeaver/ZFC/KSeedModel222.lean) (models of the derivable formulas have the seed property for equality-free relations), [`KIndisc222`](../../../Lean/BusyBeaver/ZFC/KIndisc222.lean) (indiscernibility quotient: all relations), [`KLowerSeed`](../../../Lean/BusyBeaver/ZFC/KLowerSeed.lean), [`KLowerRaw`](../../../Lean/BusyBeaver/ZFC/KLowerRaw.lean) (raw sets), [`KLowerRel`](../../../Lean/BusyBeaver/ZFC/KLowerRel.lean) / [`KLowerTag`](../../../Lean/BusyBeaver/ZFC/KLowerTag.lean) (the tagged domain `D_t`), [`KLowerEqv`](../../../Lean/BusyBeaver/ZFC/KLowerEqv.lean) / [`KLowerQHyp`](../../../Lean/BusyBeaver/ZFC/KLowerQHyp.lean) (coded bisimilarity; `D_t` satisfies [`KQHyp`](../../../Lean/BusyBeaver/ZFC/KQHyp.lean)), [`KProfileTC`](../../../Lean/BusyBeaver/ZFC/KProfileTC.lean) and `KQ1*` (the repository's quotient modules re-run on that interface), [`KQ1ZF`](../../../Lean/BusyBeaver/ZFC/KQ1ZF.lean) (ZF in the well-founded part) |
| **Endpoint** | the composition, and ZF ↔ ZFC refutation | [`KEndpoint221`](../../../Lean/BusyBeaver/ZFC/KEndpoint221.lean), [`KLower221`](../../../Lean/BusyBeaver/ZFC/KLower221.lean) |

The generators are in this directory: `generate_tables_lean.py`, `generate_dense221_lean.py`,
`generate_boot221_lean.py`, `generate_sites221_lean.py`, `generate_source221_lean.py`,
`generate_profile_tc.py` (six profile lemmas weakened to transitive containers) and
`generate_kq1.py` (the quotient modules on the `QHyp` interface). Generated data is untrusted;
the kernel re-checks it. The certificate decoder of `RMOffsetBisim` reads paths of up to 511 bits,
since the AX chain of `dag222` makes decoder paths 180 bits deep (`RMBisim.decode` stops at 127).

Compile times on this machine: `KSource221` about 60 minutes, the boot chunks about 20 seconds
each, the site batches about 3 minutes each; everything else is seconds.

### The 219

The [219](../candidate-k219/README.md) (Source 140) keeps the calculus, so the upper bound and the
semantic lower chain are reused as they are. Its endpoint
`KLower219.blank_halts_iff_zfc_refutation : BlankHalts machine219 ↔ BProv ZFCax_s [] ⊥` adds:

- **Program**: [`Dag219`](../../../Lean/BusyBeaver/ZFC/Dag219.lean) is `dag222` with the equality test (node 123) replaced
  by Source 140's routine on nodes 461–466 ([`make_dag219.py`](make_dag219.py)). The L2 modules
  are forked by [`generate_l2q219.py`](generate_l2q219.py); every lemma rechecks except the
  equality test's, which [`L2Control219`](../../../Lean/BusyBeaver/ZFC/L2Control219.lean) proves anew for the new routine
  with the old statements. [`Seed219`](../../../Lean/BusyBeaver/ZFC/Seed219.lean): `dag219_seed_iff`.
- **Source**: [`KSource219`](../../../Lean/BusyBeaver/ZFC/KSource219.lean) relates the 219's 4,744-leaf source to
  `dag219` (2,237 certificate entries, none offset).
- **Engine**: the table in K230 labels ([`lean219/`](lean219/), new states renamed into freed
  labels) changes two engine rows; [`KTape219`](../../../Lean/BusyBeaver/ZFC/KTape219.lean) reruns K230's register proofs
  against K230 patched at exactly those rows, unchanged ([`KEngine219`](../../../Lean/BusyBeaver/ZFC/KEngine219.lean)).
- **Boot, sites, bridge**: the 312,617-step startup ([`KBoot219`](../../../Lean/BusyBeaver/ZFC/KBoot219.lean), 24 blocks),
  all 4,744 decoder leaves ([`KSites219`](../../../Lean/BusyBeaver/ZFC/KSites219.lean)), and the literal
  [`Machine 219`](../../../Lean/BusyBeaver/ZFC/KDense219.lean); composed in [`KEndpoint219`](../../../Lean/BusyBeaver/ZFC/KEndpoint219.lean) and
  [`KLower219`](../../../Lean/BusyBeaver/ZFC/KLower219.lean).

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
