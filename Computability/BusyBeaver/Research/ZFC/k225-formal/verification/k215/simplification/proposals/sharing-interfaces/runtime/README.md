# Round 11: compose certified decoder entry with residual leaf checks

## Recommendation
The current phase9 work already supplies generic Home return, `execWith_sound`, and an exact universal decoder-prefix-to-zipper theorem. The practical next simplification is to **use that prefix theorem in runtime coverage**, rather than execute the decoder again in every site certificate. This is an incremental bridge, not a proposal to reprove the 281 decoder blocks or invent a second symbolic interpreter.

Keep the complete consumed program-counter word at the leaf port. Check only the residual leaf operation and return, using the existing Home-enabled executor. This deliberately does NOT claim that the 97 exposed leaf contexts are universal primitive contracts; arbitrary ancestral PC context still matters for carry/strip returns.

## Fresh owned result
Pinned source is sites215.json SHA25617af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba; native table SHA2569683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2. Independently parsing the archived formal KTable215 table and applying102→301,120→302,230→254 gave exactly all430 native rows.

`python check_residual.py` passes all6176 guards using an owned transcription of the current Home and symbolic rules:
- Full start with Home:926351 abstract steps.
- Exact leaf port with Home:705880 abstract steps.
- Avoided repeated decoder work:220471 abstract steps,23.79994%.
- Residual trace lengths:1..207 abstract steps.

An abstract step is one successful Home shortcut or one original `sstep` call, including administrative reorient/peel steps. This is NOT a count of physical TM transitions, formal proof terms, or wall-clock compile time. Home readiness is justified for this exact certified baseline, not inferred for arbitrary tables. Existing BoxLemmas remain assumed in the owned numerical checker, as in the maintained symbolic executor.

`port` routes each PC prefix through the literal table with explicit tape-window bounds and exact tape restoration at each edge. `bind_ports.py` independently parses the current maintained 202-node source array and 234-role array, follows every full source path from role0, verifies each source child, two-bit history, leaf opcode/operand and primitive action against the exact table, and obtains the `RoutedEntry` control state. The residual checker asserts its finite-prefix endpoint equals that formally routed state for every path. Thus the endpoint is NOT identified solely by a first-restored-window convention. `PORT_BINDING.json` pins this audit. The remaining formal adapter uses the existing `RoutedEntry` theorem and `routed_control_unique`; these Python checks do not recompile that theorem. All complete PC words are retained. No independent arbitrary values are substituted into interior physical configurations.

## Exact missing adapter
1. For every source leaf, select a port q with a checked `RoutedEntry`. Current `leaf_prefix`/`walk_prefix` then gives Reach from the original dispatch frame to that exact `leafPort`, uniformly over gap and register values, with unchanged whole tape. The theorem includes padded consumed PCs through `walk_prefix`.
2. Run `checkResidual` (proposal file) from that port, with initial progress flag FALSE. Existing `KHomeReady.exec_sound` and `sMatches_conc` supply a positive residual Reach1 and the exact target frame. This preserves all-natural quantification and arbitrary register/spare values.
3. Compose prefix Reach with residual Reach1. Prefix duration may be zero in the generic theorem. Never mark initial progress true solely because a prefix exists; positivity comes from the checked residual. No first-dispatch stopping criterion is used: intermediate frames may stutter.
4. Refactor the small interface between coverage and `KSim.sim_step`/`sim_halt`: introduce semantic leaf contracts, containing length/register side conditions and the concrete positive endpoint theorem for every branch. Existing `checkEdge` soundness is one producer; prefix+residual is another. Then the body of the high-level register simulation consumes those contracts instead of unfolding `checkEdge`.
5. Prove coverage for all padded walks from the literal source tree and port certificate, then reuse the unchanged register-machine relation and end-to-end source/calculus proof.

Why step4 is necessary: current `KSim.Covered` literally requires `checkEdge M Q e = true`. A semantic prefix proof plus a residual check does NOT by itself prove that the old fuel-limited evaluator returns true. Do not hide this gap by claiming the new certificate implies old Boolean coverage. Separate semantic coverage from the particular checker implementation once.

For Rocq, use the same semantic interface and certificate data at its existing runtime/source boundary, but implement the residual checker with its native zipper and reflection soundness lemmas. Do not add a Lean↔Rocq representation bridge merely to share this small optimization. This round's inspected/checked implementation is Lean-specific; no new Rocq theorem is claimed.

## Other proposals, ranked
- Spare-bit parameterization remains useful for ST/DR, but is not the most immediate simplification of the certified K215 proof. Current KTape and KRuntimeCore still hardcode append1. Threading a Boolean through the semantic box interpretation would leave `sstep`, `execWith`, `home`, normalization, and checker data unchanged, and needs the local zero-tail lemma already isolated in the prior round. This does not remove any obligation from append1 K215.
- Do not unify concrete startup and symbolic runtime into one elaborate interpreter. Startup already has generic checked `lblock` and exact concrete configurations; runtime already has generic `execWith_sound` and parametric tape interpretation. Their commonality is endpoint composition, not identical state representations. Reusing a tiny positive-Reach composition interface is preferable to new mixed-state machinery.
- Do not present exact trace memoization as a major speedup: previous full-state census found negligible sharing. This proposal saves work by an already-proved semantic prefix, not identical-state memoization.

## Status and reproduction
All Python is owned checking code; received Lean files are inert reference text. `ResidualChecker.lean.proposal` contains concrete new checker definitions but is UNCOMPILED and has no claimed Coverage theorem. No Lean compiler is available here. Baseline table/source pins are checked before replay; Python optimization is rejected. No new end-to-end proof or machine candidate is claimed.
