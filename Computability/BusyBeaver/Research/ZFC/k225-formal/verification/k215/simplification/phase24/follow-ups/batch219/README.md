# Review of the eight batch219 simplification proposals

The [placement commit](https://github.com/VladimirReshetnikov/ProveIt/commit/56b37bde8b064d852154ad8478d58ec9ab5375d6) already unpacked the eight reports and retired their ZIPs. This follow-up compares their mathematical proposals and supplied evidence with the current Lean sources. It does not repeat intake, execute submitted programs or introduce a new machine.

The strongest unimplemented idea is **sharing a decrement case's execution prefix before checking its zero and nonzero continuations**. It can use two existing executor soundness results, retaining positive progress from the prefix. It deserves a small isolated experiment inside the current simulator. The supplied 39.12% figure measures symbolic calls within the decrement workload; it establishes neither a whole-endpoint reduction nor faster Lean checking. Kernel normalization may repeat a let-bound computation, so actual benefit needs a fresh implementation and measurement.

| Reports | Finding against current sources | Action |
|---|---|---|
| `checked-local-contracts`, `contextual-contracts`, `framed-control`, `proof-sharing` | Useful guarded frame contracts and component checks; their core ideas already appear in our phase22/23 research leads. New libraries remain additive and full coverage integration is missing. | Retain research evidence; keep the current concise certificate checker. |
| `checked-interfaces` | Five normalization-first proof bodies are already adopted. Later cleanup makes the current file shorter still. | No duplicate patch; retain the negative results on the larger abstractions. |
| `consolidation-plan` | Current native Replacement is consolidated in the existing module. Generic termination transport adds a net 188 lines for one client. | Keep the current native proof; defer the larger transport library. |
| `source-identity` | AX overlays predate the shared word representation. The broad subtype framework grows the code. A direct-program decoder still lacks its main soundness and integration proofs. | Reject stale overlays; keep direct decoding as a secondary research option. |
| `proof-spine` | The generic Core/import split is already adopted and shortened. Decrement-prefix sharing remains unimplemented. | Its neutral-prefix lemma now compiles in a detached experiment; next test the paired checker. Do not restore old overlays. |

The [detached composition experiment](component/README.md) now checks one owned theorem with zero warnings and the existing standard axiom profile. It supplies the mathematical composition step only; the paired decrement checker and any checking-time benefit remain untested. The source reviews below retain their earlier uncompiled status labels.

[Control review](controls/README.md) records component costs, exact missing coverage obligations and attribution. [Semantic review](semantics/README.md), its [detailed analysis](semantics/review.md) and JSON records distinguish adopted, stale, negative and open components. Original packets remain linked at their immutable placement commit rather than copied again. Later upstream status decisions were also inspected; their source selections and counts are not substituted for ours.

The comparison binds all 230 current selected source files to phase24's frozen plan. The separate [accepted phase24 cleanup](../../README.md) removes 175 lines/8,435 bytes from 13 maintained files and passes the full kernel, actual-result and evidence checks. Those savings do not arise from this static review and are not counted again. The machine remains 215 states; the internal PA endpoint and minimality remain open.

This directory is a subsequent source review outside phase24's sealed eleven-file Lean evidence leaf and capture. Recorded component compiler results are attributed historical evidence; no submitted Lean, Rocq, checker or generator ran for this review. The active implementation language remains Lean.
