# Uncompiled lead: framed-control coverage classifier

**Source-only pilot; not elaborated, kernel-checked or adopted.** The three
[Lean sources](KControlRowsPilot.lean), [classifier](K215ControlCoveragePilot.lean)
and [mixed consumer](K215MixedControlConsumerPilot.lean) propose an exact bridge
from source controls to the existing framed-control caller family. They are
separate from phase22's accepted production-source kernel check.

The [design](pilot-design-v1.json), [static comparison](static-comparison-v1.json)
and [author's second-pass source review](review-v1.json) retain their distinct
scopes. The latter is not an independent kernel approval. The source-only
comparison finds **ordered equality**: list the actual control leaves in
false-first DFS order, remove only `(001, brk 1)` and `(11011, brk 1)`, and obtain
exactly the existing caller list mapped to full consumed word and metadata action.
Thus **1,425 − 2 = 1,423** complete rows agree in order, without sorting or a new
occurrence roster. Equal counts alone would not establish exhaustiveness. The
proposed `shared_control_rows_exact` kernel decision has not been run.

`controlRows_complete` connects `LeafAt` to that catalogue; `walk_leaf` retains
`consume P d`, including implicit trailing zeros. `control_leaf_cases` would then
classify every control leaf as an exact literal exception or a caller with the
same complete word/action. Existing caller validity and route witnesses remain
separate premises from the
[framed-control packet](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/framed-control/README.md).

The literal fallback covers **4,753 outcomes**:
`1,900 increments + 2,850 decrement outcomes + 2 controls + 1 halt`.
Adding the **20 shared template bodies** gives **4,773 projected expensive body
checks**. All 4,751 leaves and 6,176 source-outcome bindings remain required;
1,423 caller applications are not another 1,423 literal executions. No source,
proof-object or checking-time saving is established.

## Remaining production boundary

- **Full edge producer.** The residual caller theorem starts at a primitive
  `leafPort`; `EdgeContract` starts before decoding at `KSim.start`. Compose the
  [current decoder prefix](../../../../../../../../Lean/BusyBeaver/ZFC/KDecoderPrefix215.lean) with the residual,
  identify the exact route/state and full-word port, preserve the `64 − length`
  gap and marker, prove break no-overflow from the source guard, and retain
  positive progress. A physical state or short suffix alone is insufficient.
- **Consumer rebase.** Current [KSim](../../../../../../../../Lean/BusyBeaver/ZFC/KSim.lean) lacks the archived semantic
  API. Rebase the narrow
  [semantic consumer](../../proposals/semantic-coverage/lean/candidate/BusyBeaver/ZFC/KSim.lean),
  then instantiate the pilot's explicit `C` with exactly `KSim.EdgeContract tm215`.
  Its remaining `framed` premise is not discharged by residual reachability.
- **Complete fallback checks.** The separate `allSites literalGate` premise
  rejects failed decoder branches and retains both decrement outcomes and halt.
  `literalGate_of_old_sites` can initially reuse accepted coverage, but keeps the
  old certificates and claims no saving. A replacement needs fresh fallback
  batches, retaining balanced transition lookup through `KFastSites215.fast_eq`,
  followed by full coverage, endpoint and exact-profile checks.

Only inert source/data inspection has occurred. The pure-data certificate's
resource budget and all three modules' elaboration remain unverified. These research sources are separate from the maintained Lean library; the pilot
leaves production sources, machine tables and endpoint statements unchanged.
