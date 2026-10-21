# K216: partial-selector construction

**Accepted after five selected fresh checks and the independent saved-record audit passed.** This remains the reviewed partial-selector 216-state construction. The new [215-state primary contender](../candidate-k215/README.md) combines its selector with the [command-permuted alternatives](alternatives/permuted/README.md), with separate final runtime and blank-start checks.

The submitted machine has **216 working states and 432 binary transition rows, including blank initialization**, with a separate halt. Its ordinary proof composes the accepted dominated-calculus calibration, source correspondence, local selector fold, full primitive contracts, and complete startup. With the fresh obligations below discharged, the resulting claim is

```text
ZFC proves: not Halt(K216, blank) ↔ Con(ZFC).
```

This does not assert ZFC consistency, unconditional nonhalting, minimality, or a new exact-table Lean/Rocq/internal-PA endpoint.

## Exact machine

- [Canonical table](k216.tm): start 0, working labels 0–215, halt 216.
- [Native table](k216.native.tm): start 0, dispatcher 84, halt 254.
- [Canonicalization](canonicalization.json): exact bijection; native dispatcher 84 maps to canonical 84.
- [Complete source](sites216.json) and [compact serialization](sites216.compact.json): 4,751 primitive occurrences, 203 unique DAG nodes, depth 48, maximum zero run 6.
- [Reallocated prefold217 table](prefold217.native.tm), [ordinary proof](proof.md), and [provenance](provenance.json).

The convention is a deterministic two-symbol machine on a two-way infinite tape, initially all zero, with head coordinate 0 and only L/R moves. A noncomment transition row is `state read write direction next`. The halt label has no outgoing rows and is excluded from the working-state count. All 216 working states are directed-graph reachable; this does not claim blank-run visitation of each state.

| Artifact | SHA-256 |
|---|---|
| Canonical table | `5536fcf48e76f56152cfa0a77cae19c09be7161d39514075522ecfe056cffc45` |
| Native table | `2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c` |
| Spaced source | `c865047ce7283521199e93ce74307821f3b3231742213329b7ac5e8a7ec0b6d2` |
| Compact source | `7f9d4f321b7a7d56013056b1ad6be2723538c43ea2d73548bcd0e35f0381bde0` |
| Prefold table | `6cb717fe9e80be907fc80d5b85b0f36d35242dfde4723d4589ecddd2802eaae1` |

## What saves the state

The immediate parent is [accepted K217](../candidate-k217/README.md). The new source reparse exposes a selector `((A,X),(B,Y))` over 4,174 primitive occurrences. Only the zero branches A/B of the two providers are prescribed by this selector; their other branches X/Y remain live and are covered by full source/runtime verification. A further source repair retains contextual roles of native 172, allowing the prefold allocation to stay at 217 states.

Native164 and183 have the same read-one transition. Their incoming edges write distinct predecessor bits. The new read-zero path rereads that marker through existing helper201, chooses the original endpoint, and restores the complete tape in three steps. Deleting183 gives 216 states without adding a helper. The parent's69/400 reduction remains in place.

All 4,751 primitive operations and operands, all 6,175 guarded successors, the first 37 paths, and all 186 non-AX paths agree with the parent source. That all-natural source bisimulation is separate from the all-initial-tape local fold theorem, which compares the newly reallocated prefold217 table with216. A source reparse alone does not certify its physical implementation.

## Verification and reproduction

The [selected actual record](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/actual.json) and [independent saved-record audit](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/actual-review.json) record all five terminal passes and the independent review. Every freshly generated ordered runtime case and the complete startup trace equal their delivered counterparts; the runtime receipt differs only in timing.

| Obligation | Fresh result |
|---|---|
| Reconstruction | Exact source/native/dense/prefold bytes from parent and explicit recipes;20 prefold row replacements |
| Source correspondence | Complete ordered word and6,175 guarded edges; two independent CFG resolvers |
| Marker and complete blank | Exact local proof; native and dense startup313,133 transitions; dispatcher 84, head−5, gap80 |
| Whole startup frame | Registers `[3,0,0,0,3,0,0,0,0]`,130 unit spares,277 one-cells and zero exterior |
| Independent fold window | 27,527 inductive contexts,48 nontrivial1→3 blocks; corrupt initial halt rejected |
| Quantified runtime | 6,176 cases,1,709,992 symbolic rules, all 432 rows, minimum affine duration constant 13 |

The root-executed quantified replay took 178.915 seconds. The publication writer inspected its saved evidence without rerunning it. The runtime domain has independent arbitrary natural register values and gaps and any nonempty finite list of natural spare values. Unary/list induction and literal transitions establish full tape endpoints. The 4,000-rule construction cap is not a bound on represented values or concrete runtime.

The blank audit recomputes 313,133 native transitions and compares each stored trace row, then separately simulates the dense table and checks the complete tape. Its startup trace input and result are retained. The runtime driver separately recomputes its own calibrated startup. An earlier well-formed but uncalibrated frame is not the endpoint used in the theorem.

The [source result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/source/verification.json), [blank/marker result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/blank-marker.json), [fold result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/fold-window.json), and [runtime result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake195-fresh/runtime/runtime.json) retain separate obligations. See the [intake195 reproduction guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-195-reproduction.md) for direct commands, raw logs, and original recovery. The selected leaves exclude submitted manifest wrappers, ancestor suites, searches, and proof-assistant builds; the already accepted [Source149](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-191.md) and [Source152](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-192.md) records supply the inherited calibration.

## Attribution and prior search scope

The archive arrived in commit `6ec69081ca2a4abc03c35b573e22eb0d939a6324`. Its new partial-selector source, contextual repair, exact tables, reconstruction recipes, and216-specific evidence are submitted work prepared in collaboration with Vladimir Reshetnikov for ProveIt. The dominated calculus, earlier marker fold, native compiler, and symbolic runtime have inherited authorship and licenses preserved by [NOTICE.md](NOTICE.md) and [provenance/ATTRIBUTION.md](provenance/ATTRIBUTION.md).

`opening_encoder` independently reviewed the source/physical proof and code closure and authored this exposition and saved-record audit; `review_upstream_reflection` independently reviewed the full ordinary calibration. Root owns fresh execution and final publication. These roles do not transfer authorship of the submitted construction.

Earlier bounded helper searches included164/183, but capped partial-selector reparses at 600 leaves. The new 4,174-leaf region and contextual allocation repair were outside those families. Thus the prior negatives are consistent with this saving and supply no lower bound. Future searches can use partial-provider freedom while retaining every live branch and checking the actual allocation.
