# K215: 215 working states for ZFC consistency

**Accepted after full quantified runtime and independent blank-start verification.** This exact deterministic binary machine has **215 working states and 430 transition rows, including initialization**, with a separate halt. Its reviewed ordinary mathematical proof, using the inherited numerical-calculus calibration, establishes

```text
ZFC proves: not Halt(K215, blank) ↔ Con(ZFC).
```

The exact machine now also has compiled Lean and Rocq correctness proofs. These external
theorems establish halting iff ZFC has a finite refutation and nonhalting iff its
syntactic consistency. They do not assert unconditional nonhalting, a minimum-state bound,
or an internal PA endpoint.

## Checked formal proofs

**Both proof lanes pass** (2026-10-21). Lean freshly compiled all 204 project dependencies
and two explicit endpoint clients; their axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. Rocq compiled all 237 selected sources, printed
four closed endpoint assumption reports, and passed recursive `coqchk`.
The [verification page](../k225-formal/verification/k215/README.md) links the exact
statements, raw reports, retained build history, and reproduction routes.

- **Lean** (`Computability/BusyBeaver/Lean`): `KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot`, in
  [`KEndpoint215`](../../../Lean/BusyBeaver/ZFC/KEndpoint215.lean). Use the
  [serial Lean driver](../k225-formal/verification/k215/lean/README.md) to rebuild its
  complete project closure and explicit endpoint clients in a fresh workspace.
- **Rocq**: `K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent`, the variant `215` of
  [`rocq-extension`](../k225-formal/rocq/rocq-extension/README.md). Use the
  [serial Rocq driver](../k225-formal/verification/k215/rocq/README.md), including
  `--kernel`, to compile the exact source closure and recursively run `coqchk`.

The layers are described in [k225-formal](../k225-formal/README.md#the-215).

## Exact machine

- [Dense table](k215.tm): start 0, working labels 0–214, halt 215.
- [Native table](k215.native.tm): start 0, dispatcher 84, halt254.
- [Canonicalization](canonicalization.json): exact reversible renaming; dense dispatcher 83.
- [Complete source](sites215.json):202 distinct subtrees,4,751 primitive occurrences, depth47, maximum zero run6.
- [Proof exposition](proof.md), [provenance](provenance.json), and [reproduction guide](reproduction.md).

The convention is one two-way infinite tape, initially all zero, a head initially at position0, two tape symbols, and L/R moves only. Each row is `state read write direction next`. The halt has no outgoing rows and is excluded from the 215 count.

| Artifact | SHA-256 |
|---|---|
| Native table | `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2` |
| Dense table | `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090` |
| Source | `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba` |

## Construction

This combines the command-local field reader and210 command permutation from the [command-permuted K216](../candidate-k216/alternatives/permuted/README.md), delivered as `K216_Permuted_Commands_2026-10-21`, with the source reassociation of the accepted [partial-selector K216](../candidate-k216/README.md). The resulting source has exactly the ordered primitive expansion and both complete guarded control-flow graphs of the separately calibrated command-permuted source. The complete partial-selector subtree and contextual state 172 repair remain unchanged.

The new allocation retains both marker reductions:69/400 and164/183. It also uses the independently proved three-step replacement `81/0: 0L92 → 0L111`, freeing92/1 for decoder use. Relative to the accepted partial-selector216 table, it changes 35 retained rows, deletes 224, and adds no state labels. The202-node source count and the 215-state physical count are separately checked.

[Table](table_recipe.json) and [DAG](dag_recipe.json) recipes deterministically reproduce the machine without a numerical optimizer. The allocator's inherited engine census was only a synthesis filter; the fresh complete runtime proof supplies the required arbitrary-value contract.

## Fresh verification

| Obligation | Actual result |
|---|---|
| Deterministic reconstruction | Exact source, native and dense bytes; reversible state map |
| Source composition | Complete 4,751-row ordered word; both 6,175-edge guarded CFGs |
| Decoder/entry correspondence | All 4,750 internal prefixes and 4,751 primitive entries; eight local108 aliases checked |
| Quantified primitive runtime | All 6,176 cases, 1,698,790 symbolic rules, all 430 rows; minimum duration constant 6 |
| Complete blank startup |95,714 transitions, native84/dense83, head −8, header 57, gap 1 |
| Exact terminal frame | Registers `[4,0,0,0,0,0,0,0,0]`,40 one-valued spare blocks,95 one cells, zero exterior |
| Independent audit | All ordered cases, affine durations, four block schemas, exact rows, both complete blank traces |

The [root actual record](verification/root-run1/actual.json), [runtime result](verification/root-run1/runtime/runtime.json), [compressed ordered cases](verification/root-run1/runtime/runtime_cases.json.gz), [raw log](verification/root-run1/runtime.log), and [independent actual/blank review](reviews/actual-review.json) bind the released bytes. The runtime domain includes arbitrary natural register values and gaps, an arbitrary nonempty finite list of natural spare values, and the whole zero exterior. Its finite symbolic derivations use unary and list induction; the positive durations connect infinite source and binary runs. This is stronger than bounded testing, while remaining outside a proof-assistant kernel.

The [independent prospective review](reviews/review.json) and [ordinary review notes](reviews/review.md) cover source/calibration transfer and both marker constructions. The all-tape marker argument is relative to a constructed unfolding of those folds; it is not a claim that the whole reallocated table is all-tape equivalent to the previous accepted217 machine.

## History and attribution

The initial allocator gate required one global representative per logical node and rejected eight valid retained 108 occurrences. A separate local-entry reader checked their exact `101` contexts and unchanged entry rows. The original failed gate remains, together with the later reader's local 81 exception and parser-typo corrections. No machine or source bytes changed during these corrections. Pending-status drafts, the disposable solver setup, exact scripts, identity control and raw logs remain in [the research packet](research/composition-allocation/).

[NOTICE.md](NOTICE.md), [original partial-selector attribution](provenance/partial-selector/provenance/ATTRIBUTION.md), [original command-permutation attribution](provenance/permuted-commands/provenance/ATTRIBUTION.md), and [licenses/](licenses/) preserve all inherited contributions and terms. The source transformation, numerical theorem, compiler and checker ancestry are distinct from this composition and allocation. `opening_encoder` authored the composition/allocation and this exposition; `review_upstream_reflection` independently reviewed the proof and audited the actual runtime/blank evidence; root selected and ran the fresh validation and publishes the result.


Two later [composed presentations](presentations/composed/README.md) are exact
state renamings of this machine. A distinct
[DROP/NIP/MP alternative](alternatives/commands120/README.md) has its own
fresh full runtime and complete blank-start verification. Batch 198 preserves
their attribution and evidence; all three remain at215 states.

A later [distinct allocation](alternatives/composed/README.md) has the same
source and a different transition graph. Its own complete runtime/startup
passes, and an exact state bijection transfers that result to the second
submitted presentation. The new logical interfaces in batch199 remain
research toward214; they have not changed the current accepted state count.
