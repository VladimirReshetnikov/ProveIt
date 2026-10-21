# Independent review of the ordinary K215 source proof

**Result: PASS. No semantic blocker found.** The frozen `plain_source` packet proves the intended source equivalence using the ordinary equal-register segment checker. All **70** selected Lean source files match their successful compilation receipts and the frozen `result.json`.

Reviewed commit: `b6c7087477e51c017003bd729e712c8969733223`. Toolchain: `Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)`.

This was a read-only source and receipt review by a collaborator separate from the source-lane implementation. The reviewer ran independent Python parsing, exact byte comparisons, and SHA-256 verification, but did not rerun Lean. The supplied compilation receipts record the implementer's successful kernel replay. `source-review.json` gives the individual checks for all 70 modules.

## 1. What was independently verified

| Check | Result |
|---|---|
| Selected source hashes against `result.json` | 70 of 70 match |
| Per-module compilation receipts | 70 of 70 report PASS, exit code 0, and matching source hashes |
| Build log hashes | 70 of 70 match both result and receipt |
| Recorded object hashes | Match per-module receipts and dependency references |
| Packet manifest | All 233 listed files match size and SHA-256 |
| Original semantic and DAG modules | Eight are byte-for-byte identical to upstream |
| Actual `p215Nodes` and `p215` | Exact upstream declaration bodies |
| Actual `pathDagPerm` | Exact upstream definition |
| Certificate entries | All 2,240 are the exact projection of zero-offset entries |
| Certificate structure | All 16 subtree bodies and top-level composition preserved |
| Offset-module dependency | Absent from the selected import closure |

Object files are deliberately excluded from the portable packet. This review cross-checks their recorded hashes; it does not claim independent rehashing of object bytes or a second kernel run.

The unchanged upstream modules are `RegisterPath`, `RMDag`, `RMEquiv`, `RMBisim`, `Dag219`, `Dag222`, `DagDom`, and `DagPerm`.

## 2. Long paths and the decoder

`RMPlainCodec.totalDecode n` is `decodeAux n n []`. Its input-dependent fuel avoids the former fixed 128-step cap. Each nonterminal decoding step divides the code by two, so a positive input has sufficient fuel without a fixed maximum bit length.

Independent extraction found **4,480 path occurrences**, maximum path length **176 bits**, maximum sentinel-prefixed code length **177 bits**, and **622 paths longer than 128 bits**. Path length and encoded-natural bit length differ by one.

The soundness theorem is parameterized by an arbitrary decoder. It checks the decoded sites and branches against the actual program trees. Consequently, no encoder/decoder inverse theorem is assumed or required for semantic soundness. A truncated decoder would misinterpret some intended certificate paths and could prevent replay from succeeding; it does not render the generic checker theorem unsound.

## 3. Exact program binding

The program declarations remain exactly:

```lean
def p215 : Program := ⟨p215Nodes, 178, 179⟩
def pathDagPerm : Program := RMEquiv.ofDag DagPerm.dagPerm 487
```

`KSource215TreeData.lean` binds the shared trees to these actual programs with:

```lean
theorem t215_eq : ptree p215 = t215 := by rfl
theorem tD_eq : ptree pathDagPerm = tD := by rfl
```

That module has a successful receipt matching its retained source hash. The final `fwd_start'` and `fwd_all'` rewrite using these equalities before invoking the semantic theorem. The result therefore concerns the actual source programs, not unrelated proxy trees.

## 4. Zero-offset specialization and both directions

Every original offset entry has the form `(a, b, (0 : Int), j, k)`. Every new entry is its exact projection `(a, b, j, k)`. All branch cuts and successor indices are retained. The new checker verifies equal increment counts for every register using the existing `RMBisim.cntEq_ok`, exactly the zero-offset specialization of the former integer balance condition.

The resulting relation satisfies the existing `RMBisim.Bisim`. Its unchanged `Bisim.halts_iff` proves both directions explicitly:

```lean
⟨hB.halts R, hB.symm.halts R⟩
```

No reverse certificate is missing. The paired-site relation need not be a function or a bijection. Repeated left or right checkpoints are compatible with this proof.

The certificate-partition composition lemma reduces by cases on the actual certificate tree and combines the two checked child obligations. The final `allC` proof includes all 16 original subtrees; the start condition is checked separately. The DAG well-formedness partition similarly reconstructs the original `wfCheck` proposition before using unchanged semantic lemmas.

## 5. Exact final theorems and axiom reports

The final retained audit log reports:

| Theorem | Reported axioms |
|---|---|
| `KSource215PlainAudit.source_halts_iff` | `propext`, `Quot.sound` |
| `KSource215PlainAudit.source_halts_iff_iter` | `propext`, `Classical.choice`, `Quot.sound` |
| `RMPlainCodec.check_halts_iff` | `propext`, `Quot.sound` |
| `KSource215.t215_eq` | `propext` |
| `KSource215.tD_eq` | `propext` |
| `KSource215.wfCheck222` | `propext` |

The **additional `Classical.choice` belongs to the composition with the unchanged path/DAG semantics bridge in `RMEquiv`**. It is absent from the ordinary source checker and the source-to-source equivalence theorem. No new certificate axiom is introduced.

The reviewed active sources contain no `sorry`, `admit`, new `axiom` declaration, `unsafe`, `native_decide`, or `implemented_by` token. The selected logs contain no `sorryAx` or declaration-uses-sorry diagnostic. The portable build runner now rejects those diagnostics as well.

The final source statements quantify over every register file `R`:

```lean
Halts KSource215.p215 ⟨[], R⟩ ↔
Halts KSource215.pathDagPerm ⟨[], R⟩
```

and, after composition:

```lean
Halts KSource215.p215 ⟨[], R⟩ ↔
RMDag.IterHalts DagPerm.dagPerm R
```

## 6. Integration scope

The source theorem preserves the public interface used by the existing `KEndpoint215` proof. This packet is a checked simplification of that source-equivalence lane. It does **not** report a fresh build of the complete binary-machine-to-ZFC closure or a replay of the Rocq endpoint. Production integration should rebuild the affected closure and typed endpoint clients and retain the resulting axiom report.

## Frozen evidence pins

- `result.json` SHA-256: `8a6e438d8d19987c62ce43da56e78bbfc8103a7e7a416d058748cc819a78f9c9`
- `manifest.json` SHA-256: `b4ad2586b379c0eb80d17147693e896b7ad023f792bb1ea21265c16f68eacb02`
- Exact `p215Nodes` plus `p215` declaration-body SHA-256: `d05f0cfb150e149f90b3a485d58285ba2c0e22f10c96e60e563208cd3392ea92`

These pins identify the frozen packet actually reviewed. The accompanying JSON records every selected module and source hash.
