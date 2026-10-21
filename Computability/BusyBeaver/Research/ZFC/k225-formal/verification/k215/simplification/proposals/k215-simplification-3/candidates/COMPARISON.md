# Which 215-state candidate is easiest to prove?

## Recommendation

**For the shortest new formally checked endpoint, choose CM215**, native SHA-256 `e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`, dense SHA-256 `1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf`. Prove a small positive-stuttering transport from the already verified original, rather than recompiling its register machine, formula calculus, source sites, and initializer.

**For a proof genuinely rebuilt from scratch, no inspected alternative is demonstrated to be substantially simpler overall.** The original has the cleanest already-understood initialization and four directly usable commands. R41 is a plausible modest decoder-certificate improvement with unchanged command semantics, but not a simplification of the mathematical core. ST215 has a smaller command language and slightly smaller source, at the cost of a new strong compiler, a partial-AX bootstrap, and an unbounded protected-tail credit theorem. Common-pop215 has more, not fewer, source leaves than the original, and a more involved sentinel compiler. Do not select it merely because its source DAG has 201 rather than 202 nodes.

These are different goals:

1. **Incremental proof:** number of new definitions, lemmas and certificates required after importing the original theorem. CM215 clearly wins among the reviewed substantive alternatives.
2. **Total trusted dependency closure:** importing the original theorem retains its existing proof closure. Transport adds a small wrapper; it does not delete the underlying proof of the original.
3. **Independent first-principles proof:** total conceptual work when neither the original nor its compiler is available. The packets do not provide evidence that any new 215-state table drastically reduces this work.

No new Lean or Rocq compilation was performed for this comparison. The attached audit checks finite premises in owned Python, not a proof-assistant kernel. The standalone replay instructions are in `README.md`; the 22 exact data inputs and their hashes/provenance are included under `inputs/` and `INPUTS.json`, with no Git, network, or original-workspace dependency.

## Exact base and existing endpoints

The formal baseline is ProveIt commit `613f9cf28ac36eaa929f7ef909b0eb7905facc5d`:

- Native original: `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
- Dense original: `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
- Source: `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
- Lean: `SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`.
- Rocq: `tm215_halts_iff_ZFC_inconsistent`, in `CorrectDense215.v`; the sparse counterpart is `tm215_sparse_halts_iff_ZFC_inconsistent`.

The archived proof audit reports 204 freshly compiled Lean project modules and two endpoint clients, and 237 Rocq sources plus recursive `coqchk`. Its exact scope is an **external equivalence with syntactic ZFC refutability**, not an encoded internal PA or ZFC proof. This comparison relies on that existing recorded closure and does not repeat it. [B1–B4]

The original Lean endpoint is already a short instantiation of `KEndpoint.blank_halts_iff_zfc_refutation`. Its main machine-specific inputs are dense renaming, register-engine lemmas, a complete blank prefix, source-site coverage, and the source/compiler theorem. The exact source theorem is factored through `KSource215`, `L2Perm`, and the dominated-calculus comparison. Thus “factor the endpoint into reusable layers” is already implemented; the useful next simplification is **transport above those layers**. [B2–B3]

## Primary comparison

All entries below have 215 working states and 430 rows. State count excludes the separate halt and includes initialization. Source counts were freshly recomputed by reconstructing the binary source tree and counting distinct subtrees. Row deltas are native literal deltas from the original; relabellings can inflate them.

| Candidate | Native changed rows | Source subtrees / leaves | Max depth / total address length | Bootstrap | Main new obligations |
|---|---:|---:|---:|---|---|
| Original | 0 | 202 / 4,751 | 47 / 160,305 | 95,714; clean command root, N=4, all other logical registers 0 | Existing kernel closure |
| CM215 | 6 | 202 / 4,751 | 47 / 160,305 | Same 95,714 and same clean root | One radius-1 invariant, two 3-step blocks, state-map transport |
| Context215 | 5 | 202 / 4,751 | 47 / 160,305 | 95,740; same clean root | Six paired blocks, one/two-transition entry-context facts, block synchronization |
| Shallow215 | 191 | 202 / 4,751 | 46 / 159,889 | 95,740; same clean root | Context engine proof plus new decoder/source reassociation correspondence |
| R41 | 19 | 202 / 4,751 | 41 / 149,265 | Same 95,714 and same clean root | Changed decoder/site coverage plus source CFG equivalence |
| ST215 | 74 | 201 / 4,732 | 44 / 146,039 | 70,506; interior AX frame, then ten safe heads above tail 2 | New three-command compiler, partial-AX binding, debt-2 theorem |
| Common-pop215 | 74 | 201 / 4,775 | 44 / 146,483 | 70,506; interior AX frame, then ten safe heads above tail 2 | New sentinel compiler, all-command head requirement, debt 3/4 theorem |

Exact pins for every primary row are in `finite_interface_audit.json`. Native CM, context, shallow, ST and common-pop pins match the requested inputs. The audit also verified the literal original native-to-dense bijection, not merely the two hashes. [A1]

### CM215: best transport, not a smaller calculus

The source is byte-for-byte unchanged. The two old controls 52 and 176 share physical control 52; physical 176 becomes a marker selector. Define `phi(176)=52`, and `phi(q)=q` otherwise. Away from old controls 52 and 176, every target step is exactly the old step followed by `phi` on its destination. Their read-one steps agree. Only their read-zero cases expand:

- Old 52/0: marker left=1, new path `52 -> 176 -> 129 -> 154`.
- Old 176/0: marker left=0, new path `52 -> 176 -> 185 -> 168`.

Each path takes three transitions rather than one, preserves the complete tape, and has the same final head. Therefore every old step takes one or three new steps. No new AX theorem, source CFG theorem, candidate-enumeration theorem, credit theorem or startup replay is required for the new endpoint once transport is checked. The archived full 6,176-case runtime derivation is useful corroboration, but **not a necessary premise of this shortest transport proof**. [C1]

### Context215: five changed rows is not a shorter proof than six

Context215 has fewer changed rows but six distinct matched blocks. The paired old/new lengths are `(2,4)`, `(3,3)`, and four copies of `(2,2)`. Four entry guards come from single incoming writes; control 13 requires a two-transition suffix and special exclusion of too-short initial runs. The block interiors contain no modified row, making blockwise synchronization sound. Unlike CM, this is naturally a **multi-old-step to multi-new-step** simulation, not a one-old-step fixed-map simulation. Both source and theory are unchanged. Its simpler exact table is a useful transport runner-up and a source of engine-row reuse, but not obviously a shorter formal proof than CM. [X1]

Shallow215 then adds 1,042 changed addresses and an allocation change to that engine proof. The address sum improves only 416 bits (0.26%); the maximum depth drops one. A new decoder certificate or generic compiler/source correspondence is needed. The ordinary all-tape stuttering argument for context215 does **not** automatically certify shallow215. [X1]

### R41: a reasonable decoder benchmark, not a proven mathematical simplification

R41 keeps all 4,751 primitive instructions and the complete guarded CFG. It reduces maximum source-address depth 47 to 41 and address sum by 11,040 (6.89%). These are the strongest static decoder improvements among the reviewed semantics-preserving candidates. It retains the clean original bootstrap. It is therefore a more sensible from-scratch *decoder benchmark* than choosing a dirty-start candidate solely for a lower source DAG count. [R1]

But the number of source sites and 6,176 guarded cases are unchanged. Its documented constant runtime terms improve in 1,427 cases and worsen in 3,827, with 922 unchanged; no uniform speedup follows. Fewer address bits do not establish fewer proof terms or a shorter kernel build, especially if the formal checker shares prefixes. The higher theory and command compiler are unchanged. Formalize or measure before claiming a proof-size win. [R1]

### ST215: simpler command alphabet, more initialization and soundness work

ST215 replaces four-command search with three commands: transfer S, MP and AX. S has just the cache-falsity guard and returns `(h, tail(w), d, head(w))`. Its implementation has 35 rather than 78 leaves for the earlier composite transfer. But comparison to that composite is not the same as comparison to the formally checked original.

The strong compiler has to reconstruct `PUSH`, top-preserving guarded pop `H`, `DISCARD`, axiom selection, GEN, and major-first MP. It carefully handles `I(0,0)=0` and preserves an arbitrary raw underlying stack. These are real mathematical proofs, not opcode renamings. The numerical axioms and ZFC calibration remain inherited and unchanged. [S1–S2]

The 70,506-step bootstrap is shorter as a trace, but reaches ordinal 58 with logical registers `(1,0,0,0,0,0,0,18,0)` and zero spares, **not** a clean command root. It must match 177 source transitions of a synthetic AX from raw tail 2. AX completes with ten theorem heads over that opaque tail; the scheduler has exact conservative debt 2, leaving margin 8. The tail has buried falsity, so a theorem-stack argument without the credit proof is unsound. The inherited generic protected-tail exposition has an illustrative tail-4 bootstrap; instantiate its arbitrary-tail theorem with the actual tail-2 receipt, rather than copy the old numerical example. [S1–S3]

Thus ST is a plausible research choice for a cleaner three-command presentation, not the shortest route to an additional kernel endpoint. Removing 19 of 4,751 leaves and one of 202 source subtrees is too small by itself to justify replacing the established compiler and adding the credit bridge.

### Common-pop215: do not favor it for proof simplicity

Its common guarded pop changes MP to consume the major from the stack and makes AX consume its generalization premise. Every command, not only transfer, needs a protected head. The compiler must maintain a zero sentinel and a non-1 cache, prove the multi-stage K macro, use a special `J(0)=R` rather than MP(0), and carry the exact zero-alias bookkeeping through MP and GEN. It uses the original numerical axioms, not a smaller theorem calculus. [P1]

Its conservative weights are R=-1, M=-1 and A=+9. A has an additional internal pop; the proved debts are 3 at command boundaries and 4 internally. Ten protected heads over tail 2 leave margins 7 and 6. In contrast ST's balance is S=-1, MP=0, AX=+10 and its debt is 2. [P1–P2]

Common-pop has 43 more leaves than ST and 24 more than the original, despite its 201-subtree DAG. Its 6,209 guarded runtime cases exceed the original's 6,176. Both changes are small numerically; their importance is that they refute any automatic inference from “201 source nodes” to “easier proof.” It is an interesting state-allocation direction, not my recommendation for proof simplification.

## Secondary inspected alternatives

- **Rho6-120/210:** only two native rows and four source operands change relative to their respective parents, but a fixed AX tuple now emits a different sixth row. Equality of the complete axiom family requires parameter surjectivity on all naturals and a repaired selector/compiler proof. This is not an all-tape local-equivalence patch. The original clean root is retained; the logical calculus is extensionally the same. Two changed rows are not enough to outrank CM's two exact blocks. [Q1]
- **Zero-spare MP-first215:** a one-row spare change relative to its MP-first parent does not connect it directly to the verified original. Its start is native 74, and after 73,172 steps it reaches an AX interior with dirty cache 1 and other nonzero working registers. A 177-step source prefix, AX completion to eight protected theorem heads, and the MP-first debt-one theorem are essential. Lower debt does not remove the harder startup interface. [Z1]
- **Rotated215:** unchanged source CFG and theory, but startup takes 716,307 steps and reaches a root with numeric parameter D=1. Its safe-parameter extension is mathematically reasonable, but it adds work over the original's clean root. [T1]
- **Context archive's 201-subtree/4,709-leaf cache-return source:** no accepted physical 215-state implementation is supplied. It must not be offered as an easier *215-state machine*. The membership-alarm and parity/disequality source experiments likewise are not accepted substitutes for the requested exact machine. [X1]

The comparison is over the named inspected packets, not an exhaustive ordering of every 215-state table in existence.

## Concrete transport interface and implementation plan

### 1. Make the marker invariant one-step inductive

The archive's two-history explanation can be replaced by this state-local radius-1 invariant on the **old** run:

- if q=52, the left neighbor is 1;
- if q=156, the right neighbor is 1;
- if q=176 and the current symbol is 0, the left neighbor is 0.

The middle clause is the useful strengthening. The only incoming row to 156 is `189/1 = 1 L 156`; it establishes right=1. Hence its outgoing one-branch returns to a known 1, and cannot violate the conditional 176 assertion. The other incoming writes establish the left markers directly. State 0 satisfies all clauses on every tape.

Our finite owned audit checked preservation on every satisfying five-cell neighborhood: 6,840 accepted premises among `215 * 32 = 6,880` possible state/neighborhood inputs. Only radius-2 windows are needed to check the radius-1 property after one head move. It separately checked the exact six-row delta, unchanged rows up to phi, both finite blocks and original/dense literal identity. No inherited executable was run. [A1]

A more general implementation can store an 8-bit mask of allowed `(left,current,right)` triples for each control. Initialize all eight triples at start 0; compute an overapproximation by finite abstract reachability with the new exterior bit nondeterministic. A small kernel checker verifies inclusion of all start triples and closure for all five-bit windows. Exact reachability is unnecessary: any closed overapproximation strong enough for the two blocks works. The explicit three-clause invariant is already sufficient, so mask synthesis is an engineering convenience, not an extra mathematical premise.

### 2. A generic positive-step transport theorem

Use existing machine semantics. Abstractly, provide:

- deterministic old and new step functions;
- initial configurations `s0`, `t0` and a boundary map `F` with `F(s0)=t0`;
- an invariant `I` true at s0 and preserved by each old step;
- terminal equivalence under F on I-states;
- for every nonterminal old step `s -> s'` with I(s), a positive finite new execution `F(s) ->+ F(s')`.

Then `Halts old s0 iff Halts new t0`. A uniform upper bound is not required for the generic theorem, though CM has one or three steps. Positivity prevents an infinite old execution from collapsing to finitely many new steps. The target execution must not halt in block interiors; a literal successful n-step execution already supplies this for these deterministic partial-step semantics.

The reverse implication is not an assumed inverse map: phi is deliberately noninjective. Derive it by deterministic finite-prefix synchronization. Given a target halt after h steps, follow at most h+1 source transitions. If source has not halted, positivity gives more than h target steps, contradicting the target halt. This avoids needing a separately postulated infinite run or inverse state reconstruction.

For CM, F preserves the whole tape and head and changes only q by phi. No invariant on the target's marker-selector intermediate configurations is needed. Source halt 254 maps to target halt 254; all source working states map to working states. These terminal facts must be included explicitly.

### 3. Integrate without rebuilding the enormous lower layers

Suggested Lean modules, names provisional:

- `KTransport`: generic reachable-invariant/positive-stuttering theorem for `KZip`.
- `KMarker215`: the six changed rows in the existing sparse label convention, three-clause invariant, two local blocks, and halting equivalence.
- `KDenseMarker215`: literal 215-state dense table and checked dense/sparse renaming.
- `KEndpointMarker215`: composition of `marker_blank_halts_iff_original` with `KEndpoint215.blank_halts_iff_zfc_refutation`, then negation.

Rocq can mirror the same four parts, reusing its existing sparse and dense semantics and `tm215_sparse_halts_iff_ZFC_inconsistent` or the dense endpoint.

**Important representation detail:** native archive labels use halt 254 and spare labels 301/302. Lean's existing K230-labelled runtime renames these to halt 230 and labels 102/120. Use the already audited bridge, or explicitly check that same bijection for the patched table; do not compare dense row numbers to native controls 52/176. The CM archive's own dense numbering differs from the original dense numbering. Finite commuting diagrams must bind the actual table bytes.

**Tape-scope detail:** Lean `KZip` uses trimmed finite-support list tapes, whereas Rocq's inherited tapes are streams. Proving the transport on all `KZip` configurations is enough for the blank endpoint and keeps the proof small. Do not claim that such a Lean statement quantifies all infinite binary tapes. The broader archive theorem can be proved in a functional/stream tape semantics separately if desired; adding that bridge is unnecessary for this task.

### 4. What to test and measure

Compile the new transport modules and explicit clients; print assumptions; run the Rocq recursive checker. Confirm the literal candidate hashes and both directions of the halting theorem. Keep a deliberately corrupted marker bit/row test so the finite checker is known to reject a broken certificate. Do not replace kernel decisions with a Python success flag.

Measure *additional* source size, proof object size, fresh kernel time, peak memory and total transitive closure separately. The expected win is a very small additional certificate and theorem instead of another 95,714-step bootstrap and another source/runtime development. A claim about the total proof becoming smaller needs separate refactoring or a from-scratch comparison and is not established here.

## Sources and evidence

### Repository sources, pinned to the verified base

All B links use commit `613f9cf28ac36eaa929f7ef909b0eb7905facc5d`.

- **B1:** [Formal correctness README](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md).
- **B2:** [Lean KEndpoint215](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean).
- **B3:** [Generic KEndpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean), [KZip](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZip.lean), [KDense215](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean), [KTable215](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean).
- **B4:** [Rocq CorrectDense215](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v).

### Local received packets

These paths are from `/workspace/scratch/416780682817`. They were read as data/text only. The context ZIP was read through Python `zipfile` without executing code. These are provenance paths, not replay dependencies: every table/source/map consumed by the shipped checker is copied byte-for-byte under `inputs/` and pinned in `INPUTS.json`. The narrative source reports remain cited at their original packet locations.

- **A1:** `research_proof_simplification/candidates/audit_candidate_interfaces.py` and `finite_interface_audit.json`; independently written finite audit dated 2026-10-21.
- **C1:** `research_sub214d/intake/ZFC_Conditional_Marker_215_2026-10-21/ZFC_Conditional_Marker_215_2026-10-21/README.md`, `proof/marker215-proof.tex`, `machine/marker215.native.tm`, `machine/marker215.tm`.
- **X1:** `research_sub214d/intake/context_transfers.zip`, internal root `ZFC_K215_Context_Transfers_2026-10-21/`, especially `README.md`, `report.tex`, `code/verify_context.py`, `machine/sites215.json`, `machine/sites-shallow.json` and both tables.
- **R1:** `research_sub214d/intake/ZFC_K215_Rebalanced_2026-10-21/ZFC_K215_Rebalanced_2026-10-21/README.md` and `machine/`.
- **S1:** `research_sub214d/intake/ST215_Direct_Transfer_2026-10-21/ST215_Direct_Transfer_2026-10-21/README.md` and `evidence/bootstrap.json`.
- **S2:** Same ST root, `proofs/transfer_compiler.md`.
- **S3:** Same ST root, `proofs/protected_credit.md` (generic theorem; distinguish its historical tail-4 illustrative bootstrap from the final tail-2 receipt).
- **P1:** `research_sub214d/delivery_packet/README.md` and `proofs/PROOF.md`, especially §§2–9.
- **P2:** Same common-pop root, `proofs/CREDIT_PROOF.md` and exact machine/source files.
- **Q1:** `research_sub214d/intake/K215_Rho6_Permutations_2026-10-21/K215_Rho6_Permutations_2026-10-21/README.md`.
- **Z1:** `research_sub214d/intake/K215_Zero_Spare_MP_First_2026-10-21/K215_Zero_Spare_MP_First_2026-10-21/README.md` and `machine/startup_summary.json`.
- **T1:** `research_sub214d/intake/ZFC_215_R6_and_Short_Transfer_2026-10-21/ZFC_215_R6_and_Short_Transfer_2026-10-21/README.md` and `machine215/PROOF.md`.
