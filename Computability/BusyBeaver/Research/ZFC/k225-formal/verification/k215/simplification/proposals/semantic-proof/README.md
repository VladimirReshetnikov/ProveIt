# K215 proof simplification: semantic interfaces and smaller imports

Research and implementation packet for ProveIt, 21 October 2026.

**Baseline:** [`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`](https://github.com/VladimirReshetnikov/ProveIt/tree/2ca3a5c16f0876d2cab842056353c03a1ed2f5f0).  
**Checked toolchain:** Lean 4.32.0, Linux x86-64, compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Start with [report.pdf](report.pdf); [report.tex](report.tex) is its complete editable source. The report explains the mathematical interfaces, checked changes, measurements, provenance findings, and Rocq port plan. The three proposal directories can be reviewed independently.

## Recommendations and present status

| Priority | Proposal | What is established in this packet |
|---|---|---|
| 1 | Separate ZF model semantics from the old 254-state program proof | A four-file import patch, a verbatim theorem move, preserved legacy clients, and a smaller K215 source import closure. |
| 2 | Make the simulation consume semantic site contracts | Checked `KSim` refactor and old-interface clients; composition with the maintained decoder-prefix theorem; a guarded CB1 primitive pilot. Complete primitive-family coverage remains an explicit obligation. |
| 3 | Share the named-calculus derivations | One generic development, checked specializations for both calculi, and a downstream restricted-calculus client. This reduces duplicated reasoning but initially increases combined source length. |
| 4 | Align and simplify Rocq | A source/receipt audit and a concrete plan to port the semantic interface over the existing stream-tape semantics. No new Rocq compilation is supplied. |

The existing endpoint equates blank-tape halting of the literal machine with a finite ZFC refutation. Negating both sides gives its syntactic consistency equivalence. These proposals preserve that statement. They do not supply a new internally encoded derivation inside ZFC or PA, a smaller machine, or an unconditional proof of nonhalting.

### Immediate import reduction

`ConstructibleChoice` imports `ZFNative` for `ZFNative.models_ZF`, thereby importing the older program calibration. `KQ1ZF` also reaches that layer through an unnecessary `WFTheory` import. The patch moves `models_ZF` verbatim into `ZFModelSemantics`, retains its original namespace and name, makes the legacy facade import it, and narrows the two semantic consumers.

| K215 source import closure | Before | After | Net reduction |
|---|---:|---:|---:|
| Project modules | 192 | 181 | 11 |
| Source bytes | 2,363,203 | 2,164,693 | 198,510 |
| Source lines | 45,143 | 42,010 | 3,133 |

Twelve old modules leave this closure and one small module enters. The old files remain available for legacy clients. These are source-import measurements, including comments and data; they are not theorem-term sizes, axiom reductions, or measured compilation speedups.

### Semantic sites and the CB1 pilot

The current `Covered` predicate demands acceptance by a particular bounded symbolic executor. A direct proof of concrete primitive behavior need not imply that executor's acceptance. The refactor introduces `RunContract`, `PortContract`, `EdgeContract`, and `SemanticCovered`, proves the Boolean-to-semantic adapter, and places the shared simulation proof behind that semantic interface. The original public simulation theorem types remain available.

Successful nonhalting source steps retain **positive** physical reachability. A decoder prefix may take zero steps; the whole macro step must make progress for the reverse halting implication. Contracts also retain the complete consumed source word, branch conditions, gap, and register effects. Grouping sites solely by physical entry state or a short suffix would lose continuation information.

`KSemanticSites215` proves integration theorems with an explicit `PrimitiveContracts` parameter. That parameter has **not** been discharged for every family. The census finds 4,751 literal leaves, 6,176 branch outcomes, and 135 candidate primitive role outcomes. The latter count measures potential sharing; it is neither 135 completed proofs nor a measured speedup. The census walks the source DAG and separately counts primitive role entries; it does not replay the full source-to-role routing proof.

`KCB1Suffix` and `KCB1Contract` implement a checked first family for words `A001` at state 108 reading `1`, returning along the source continuation `A1`. Their theorems quantify over arbitrary gaps and register values. They retain these premises:

```lean
leftCheck tm215 1 (A.reverse ++ [true]) 2 = true
A.length + 3 ≤ 48
```

The composed edge theorem also requires the exact source-leaf and routing facts. Certifying those facts and guards for all 86 proposed CB1 occurrences is still required before retiring their existing site checks. The archive therefore contains checked infrastructure and a guarded primitive theorem, not a completed replacement of `KSites215`.

### Shared logic

`NamedDerived` parameterizes the repeated classical and quantifier reasoning. Its vacuity theorem carries explicit equality-atom admissibility: the unrestricted client permits equality atoms, while the restricted client uses the equality-free specialization. The factorization does not add unrestricted equality-vacuity to the smaller calculus.

The production files change from 503 to 599 lines and from 21,694 to 23,660 bytes. Thirty-eight derived-rule bodies become compact transparent aliases; the two vacuity declarations remain theorems. Adopt this prototype for proof sharing and maintenance, with its initial 96-line cost visible. The import cut is the immediate size reduction.

## Archive layout

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Main report, mathematical arguments, source links, and adoption sequence. |
| `proposals/import_cut/proof/` | Four-file Lean overlay, including the new `ZFModelSemantics`. |
| `proposals/import_cut/tests/` | `ImportCutAudit.lean`, exercising the moved theorem, semantic clients, and legacy facade. |
| `proposals/import_cut/semantic_import_cut.patch` | Patch against the pinned checkout. |
| `proposals/semantic_sites/proof/` | `KSim`, `KSimCompatibility`, `KSemanticSites215`, `KCB1Suffix`, and `KCB1Contract`. |
| `proposals/semantic_sites/semantic_sites.patch` | Complete five-file semantic-interface and pilot patch. |
| `proposals/named_logic/proof/` | `NamedDerived`, `TarskiDerived`, `KThmK`, and `NamedDerivedAudit`. |
| `proposals/named_logic/named-derived.patch` | Three production files; the audit client is supplied separately in the overlay. |
| `scripts/` | Targeted Lean checker, import-cut generator, source/receipt audit, machine census, and packet verifier. |
| `evidence/measurements/` | Import graphs and metrics, primitive census, unchanged-definition hashes, logic accounting, and source/receipt comparisons. |
| `evidence/checks/` | Raw final ledgers for `base`, `import_cut`, `semantic_sites`, and `named_logic`, with portable log maps. |
| `evidence/logs/` | Deduplicated original compiler logs referenced by the log maps. |
| `evidence/verification_summary.json` | Compact status and verification scope. |
| `evidence/history/` | Rejected development targets, clearly separated from final accepted results. |
| `provenance/` | Exact original uncompiled CB1 draft and its upstream archive identity. |
| `notices/`, `NOTICE.md` | Preserved attribution and inherited terms. |
| `SHA256SUMS` | File-integrity manifest. |

Compiler binaries and compiled proof objects are omitted. This packet is intended to accompany the pinned ProveIt sources.

## Verification scope

| Accepted proposal check | Selected modules | Scope |
|---|---:|---|
| Import cut | 123 | 99 fresh compilations and 24 exact matched providers; generic `KEndpoint`, semantic ancestors, legacy `ZFNative`, and `ImportCutAudit`. |
| Semantic sites | 27 | Final closure of `KSimCompatibility`, `KSemanticSites215`, and `KCB1Contract`, with original logs for accepted providers. |
| Shared named logic | 16 | 13 fresh compilations and 3 exact matched providers; `NamedDerivedAudit` and the actual `KEind222` consumer. |

These are separate checks of their respective overlays, not a combined production checkpoint. The concrete machine-specific `KEndpoint215` closure was not rebuilt, and no new Rocq kernel run is claimed. The unchanged baseline provider check contains 24 modules. Counts for different checks overlap and should not be added as unique-module counts.

The reported prototype assumption lists contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`; the accepted prototypes introduce no `sorry` or new postulate. The explicit `PrimitiveContracts` hypothesis remains a mathematical obligation even though it is not a global axiom.

Raw ledgers preserve original absolute paths and command lines as historical evidence. Each adjacent `log-map.json` maps its modules to bundled logs using portable packet-relative references. Some accepted machine modules were compiled successfully during earlier development runs whose later targets failed; only the final accepted source fingerprints and matching provider logs support the final result. The original rejected target is not thereby certified.

Do not use the delivered evidence directories as `--reuse` providers: their compiled objects are deliberately absent. Fresh reproductions should write new receipts and objects to their own output directories. Reuse between your own subsequent runs is supported only after compiler identity, transitive source/import fingerprints, and object hashes match.

## Reproduce the checks without changing the checkout

Use a clean checkout at the pinned commit and the complete Lean 4.32.0 Linux distribution. The Python scripts use the standard library. `check_lean.py` relies on Linux `fcntl` locking and the distribution's `lib/lean/libleanshared.so`.

Run the following from the extracted packet root, choosing a new output directory outside it:

```sh
PROVEIT_REPO=/absolute/path/to/ProveIt
LEAN_BIN=/absolute/path/to/lean-4.32.0-linux/bin/lean
RESULT_ROOT=/absolute/path/to/new-k215-check-results

git -C "$PROVEIT_REPO" rev-parse HEAD
"$LEAN_BIN" --version
sha256sum -c SHA256SUMS
python3 scripts/verify_packet.py --repo "$PROVEIT_REPO"
```

The expected Git revision is `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`. Each overlay is resolved before the four repository source roots. No patch application is necessary for these commands:

```sh
python3 scripts/check_lean.py \
  --repo "$PROVEIT_REPO" --lean "$LEAN_BIN" \
  --out "$RESULT_ROOT/import_cut" \
  --overlay proposals/import_cut/proof \
  --overlay proposals/import_cut/tests \
  --target BusyBeaver.ZFC.KEndpoint \
  --target BusyBeaver.ZFC.ZFNative \
  --target ImportCutAudit

python3 scripts/check_lean.py \
  --repo "$PROVEIT_REPO" --lean "$LEAN_BIN" \
  --out "$RESULT_ROOT/semantic_sites" \
  --overlay proposals/semantic_sites/proof \
  --target BusyBeaver.ZFC.KSimCompatibility \
  --target BusyBeaver.ZFC.KSemanticSites215 \
  --target BusyBeaver.ZFC.KCB1Contract

python3 scripts/check_lean.py \
  --repo "$PROVEIT_REPO" --lean "$LEAN_BIN" \
  --out "$RESULT_ROOT/named_logic" \
  --overlay proposals/named_logic/proof \
  --target BusyBeaver.ZFC.NamedDerivedAudit \
  --target BusyBeaver.ZFC.KEind222
```

Each command emits `verification.json`, per-module logs, and an isolated `objects/` directory under its `--out` path. A fresh reproduction will compile modules that the original session reused; its fresh/reused split and elapsed time need not match the historical receipt. The module closure and mathematical targets should match.

To inspect patch applicability, set the packet's absolute location and run:

```sh
PACKET_ROOT=/absolute/path/to/extracted-packet

git -C "$PROVEIT_REPO" apply --check \
  "$PACKET_ROOT/proposals/import_cut/semantic_import_cut.patch"
git -C "$PROVEIT_REPO" apply --check \
  "$PACKET_ROOT/proposals/semantic_sites/semantic_sites.patch"
git -C "$PROVEIT_REPO" apply --check \
  "$PACKET_ROOT/proposals/named_logic/named-derived.patch"
```

Apply selected patches in a review branch when adopting them. The semantic and logical overlays are independent prototypes; perform the repository's maintained endpoint checks after selecting and integrating a combined production checkpoint.

## Reproduce the static measurements

These commands read the pinned checkout and write new evidence outside the packet. They do not invoke Lean or Rocq:

```sh
mkdir -p "$RESULT_ROOT/measurements"

python3 scripts/prepare_import_cut.py \
  "$PROVEIT_REPO" "$RESULT_ROOT/measurements/import_cut"

python3 scripts/audit_machine.py "$PROVEIT_REPO" \
  --output "$RESULT_ROOT/measurements/machine_census.json"

python3 scripts/audit_snapshot.py \
  "$PROVEIT_REPO" "$RESULT_ROOT/measurements/snapshot_audit.json"
```

`prepare_import_cut.py` regenerates the proposed import overlay, patch, and before/after source graphs. `audit_machine.py` counts the literal source and role data. `audit_snapshot.py` compares current source hashes with archived checkpoints, validates the relevant recorded archive hashes, and reads archive members without executing archived code.

At the pinned commit, 196 of the phase-nine Lean union's 197 source files match; `DominatedImplication` is the later replacement. The retained Rocq tree matches 41 of the original local lane's 42 modules. Against the normalized 44-module successor, 34 match, six differ, and four are absent. These comparisons identify different source checkpoints; a mismatch is not evidence of an incorrect proof. Reconcile the chosen Rocq source lane, templates, and generated files before replaying its kernel audit.

## Rebuild the report

Use a standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, `geometry`, `microtype`, `booktabs`, `longtable`, `tabularx`, `enumitem`, `listings`, `fancyhdr`, `xurl`, `hyperref`, and TikZ. No external image assets or bibliography tool are required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Two passes resolve the table of contents and references. The distributed PDF was rendered and visually inspected. Rebuilding changes generated files, so verify the distributed `SHA256SUMS` before rebuilding; it records the delivered bytes rather than promising a byte-identical TeX output on every system.

## Attribution and adoption

The existing enumerator, compiler, machine, proof infrastructure, and prior simplifications remain work of the ProveIt project and the contributors credited in its notices. Existing normalized certificates, the exact decoder prefix, shared Home return, the compact implication derivation, and earlier parameterization proposals are credited in the report. See `NOTICE.md` and `notices/` for inherited attribution and terms.

The recommended first change is the import cut. Next establish the semantic interface with existing site certificates intact, complete the finite CB1 routing/guard coverage, and replace repeated executions family by family. Measure net source and build savings only after those clients are actually removed.
