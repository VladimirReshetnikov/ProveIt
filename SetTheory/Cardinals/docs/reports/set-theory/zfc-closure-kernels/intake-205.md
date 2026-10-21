# Supplementary reconciliation of batch 205 proof proposals

This review reconciles Sources 168–173 with the maintained K215 proof and its simplification phases 2–5. The six archives arrived at `a6b3a30011` and were already placed by upstream commit `35ba151c3bd6289161e0c1eee864ac4328e611a0`, under the [proof-proposal directory][proposals]. The supplemental recovery placement is committed as `0359ebda60aaf52758358e1450a04988136db67e`; its control verifies all 851 members. This written supplement adds interpretation and review without another payload copy. The separately revised batch 206 packet is discussed as Source 174 in the appendix.

The useful new Lean directions are a source certificate modulo implicit trailing zeros, a small context-sensitive decoder certificate, and semantic rather than syntactic formula round-trip transport. Other proposals independently corroborate existing simplifications or provide relative proofs for existing 215-state alternatives. None supplies a verified machine below 215. The current task is to simplify Lean proofs; Rocq material is preserved and described as historical evidence, without scheduling a new Rocq implementation.

Our own review was read-only: an in-memory inventory of 851 archive members, selected complete mathematical/checker source reads, current-source comparisons, and bounded literal censuses. No delivered script, proof compiler, search or full runtime checker was executed. Delivered kernel receipts remain delivered evidence, distinct from the repository’s compiled endpoint and the phase 5 checkpoint. No full imported-object closure was independently reconstructed for these proposals.

## Placement, recovery and overlapping material

| Source | Upstream proposal directory | Archive members | Expanded bytes |
|---|---|---:|---:|
|168/A|[k215-simplification][A]|165|4,600,743|
|169/B|[k215-transport][B]|146|4,497,136|
|170/C|[structural][C]|97|5,673,975|
|171/D|[zfc215-simplification][D]|187|7,962,759|
|172/E|[zfc-k215-transport][E]|123|4,242,617|
|173/F|[fm215-compression][F]|133|2,299,159|

The arrival ZIPs remain recoverable from immutable Git history. Upstream’s placement README records that logs were omitted by ignore rules and that selected E reference files and F inherited notices/tables were omitted as repository copies. Consequently, “placed whole” must not be read as saying every archive member exists beneath each proposal directory. The supplemental member map should distinguish exact placed bytes, verified preexisting aliases and arrival-ZIP fallback. Main reports are already retained by that upstream placement; this supplement does not reorganize them. The [supplemental recovery map][map205] now covers all 851 members: 649 upstream references, 123 immutable prior aliases, 46 occurrences supplied by 41 exact ancillary files, and 33 arrival-ZIP fallbacks. Four Source 171 dependency files differ from the corresponding upstream placed bytes; their original versions are preserved separately, without inferring why they differ. Narrow raw-text attributes preserve these original CRLF `.v` bytes in Git; neither version was normalized. Opening’s recorded [recovery control][recovery205] compares every route with its original ZIP member; this is fresh recovery evidence, not a delivered-proof replay.

Our earlier placement-planning census found 342 member occurrences matching verified current tracked files, 17 additional duplicate occurrences among unmatched ancillary payloads, and 470 unique ancillary contents. It proposed 22 main-document members as archive-only. These are planning categories, not a description of upstream 35ba’s actual placement. Alias checks read current file bytes, including 25 modified proof/generator files, rather than assuming HEAD still matched. The inventory found no unsafe archive names, symlinks or compiled proof/Python objects. Original manifests, notices, failed attempts and delivered receipts remain attribution and recovery material; they are not fresh validation.

## Source 168: normalize certificate pointers without changing execution

The strongest immediately usable contribution is the [normalized source checker][normalized]. It observes that source pointers denote infinite bit streams padded by zeros. Different finite lists can therefore refer to the same instruction. The existing `RMEquiv.ipeq` relation captures this equality; the proposed Boolean comparison proves that relation rather than literal list equality.

The important lemma preserves both parts of `tsite`: the instruction and the complete path consumed while finding it. The certificate relation is saturated by `ipeq` in both coordinates: a pair of current pointers is related when some stored representative pair is equivalent to it. Segment execution retains the existing positive finite segment bound and exact per-register increment counts. Entry obligations transport the complete `tsite` observation, and the existing `RMBisim.Bisim.halts_iff` supplies both directions for every natural-valued register file. No finite-register, well-formed-program, blank-start or source-reachability premise is hidden in this generic theorem.

This reduces the concrete certificate from 2,240 entries to 1,426: 1,425 decrement checkpoints and one halt, removing 814 representation aliases. It is not the separate 1,423-class effect-graph experiment. That smaller graph has no corresponding kernel theorem in the inspected material.

Our full read of the 161-line generic checker found no mathematical defect. Opening independently checked its proof structure, the 1,426-entry data shape and the eight exact program declarations against current sources. Six of eight dependency snapshots still match; `RMEquiv` and `RMBisim` changed in phase 5. The delivered incremental kernel receipt therefore does not establish the present closure.

The integration should retain phase 5’s decoder-parameterized API and old 128-decoder compatibility. Add normalization over the same explicit decoder, using 512 for this certificate. Crucially, apply `incPath` and `breakPath` to the **consumed path returned by `tsite`**, never directly to a stripped representative. Ordinary pointer equivalence does not license arbitrary syntax operations on representatives. Shared-tree organization is a separate representation change. A fresh certificate check, unchanged all-register public theorem and both endpoint clients remain required. Fewer entries alone do not prove a proportional reduction in kernel time or memory.

Source 168 also supplies CM215 relative proofs, dense/Core adapters and positive-stuttering infrastructure. Those are alternative proofs of an existing machine, not additional source-certificate savings or a newly smaller table.

## Source 169: exact relative transport and bounded search

Source 169 develops another CM215 proof using three marker conditions and positive blocks. This is stronger than agreement on a long blank trace: its native theorem starts at control 0 with an arbitrary tape and head, maintaining the complete tape at synchronization boundaries. It also supplies an actual dense/Core bridge. Its final short ZFC wrapper is explicitly uncompiled in the delivered record; neither that wrapper nor the full inherited endpoint closure has been replayed here.

The reusable principle is mathematically appropriate. Every old step becomes at least one new step, related states agree on halting, and target halting persists. Induction yields synchronization times at least as large as the old step count, so a target halt cannot remain forever between synchronization boundaries. Positivity is essential; a zero-length simulation would not provide this reverse implication. The generic Coq 8.18 result is separate from any concrete maintained Rocq 9.1 endpoint.

The source-graph proposal records 32 local effect signatures and 1,423 stable classes. These are finite measurements, not an implemented replacement for the source semantics. Its reported 17,708,928 fold specifications and 159,509,360 branch specifications are bounded negative search results; branch specifications are not distinct machines. Radius 7 and fuel 97 constrain the tested relation. Failure to join within those bounds is not generally a semantic counterexample and establishes no state-count lower bound.

## Source 170: smaller semantic interfaces and context-aware sharing

Source 170 offers several distinct proposals rather than one compiled replacement. Its canonical weighted test graphs agree at 1,426 vertices and 2,850 edges, including initial point, effects and primitive ordinals. The proposed proof route derives the existing bisimulation from canonical ordinal agreement. This needs an adequacy theorem; it cannot be replaced by equality of instruction strings. The two programs differ at 855 primitive-word positions through continuation retagging and commuting increments. Moreover, using canonical pointers with the unmodified raw checker fails 5,324 of 5,700 endpoint-side comparisons. This explains why Source 168’s saturated relation is substantive.

The [semantic round-trip patch][roundtrip] is a smaller, independent opportunity. `KSeedModel222` can choose the original named bundle and use existing `sat_encode_decode`, instead of separately proving two syntactic round-trip inductions. A current Lean search found no consumers of `enc_dec_enc` or `eqFree_dec_enc` outside their local implementation. The estimated 25-line reduction remains uncompiled and must preserve the actual bundle theorem and public clients. Related proposals factor classical/quantifier interfaces and transport seed semantics. They must retain quantifier/equality admissibility guards, require surjectivity and relation reflection where used, and preserve the exceptional coincident-public-label case: the relevant bundle equivalence is two-sided for distinct labels but only the established forward direction is available generally.

The decoder proposal is concrete and aligns with our independent census. A source subtree alone is insufficient: the same subtree may have different break/continue ports, and physical states can depend on preceding bits. The key is `(source DAG node, physical control, last up-to-two predecessor bits)`, with the root marker history fixed. It has 234 reachable roles, 371 internal-edge rules and 97 primitive-entry rules. This preserves all 4,751 leaf occurrences; it does not confuse them with 202 distinct source subtrees.

The packet also proposes observing a symbolic endpoint once rather than running the checker twice. That needs a sound compositional interface retaining positive movement and all target conditions. Delivered profiling reports only 295 repeated exact symbolic states among 2,442,801 steps, which limits the appeal of simple whole-state memoization. The startup sweep compression and corrected increment-reversal prototype are useful finite representations, not demonstrated kernel speedups. These formalization proposals are explicitly uncompiled.

## Source 171: ordinary source proof and M124

Source 171’s principal delivered result is an ordinary, one-sided Rocq source correspondence with a compact path codec and exact expansion equality. It reports 173,003 certificate-source bytes instead of 1,499,170. That is a representation measurement, not an object-size, whole-proof or timing result. The recorded compatibility environment is Coq 8.18; the retained original 9.1 path was not run. Separate codec and mirror checks passed as delivered, while a separately recursive whole-source check was not completed; an optional prior attempt was interrupted after 409.2 seconds. No stronger current Rocq claim follows.

For Lean, removing zero offsets with an adequate decoder is already phase 5 work, and deriving the reverse simulation from symmetry is already phase 2 work. Repeating those recommendations adds no new proof reduction. Shared data or abstract composition may still be evaluated separately.

M124 is an existing four-row marker variant, with a two-clause marker invariant and positive one/three-step blocks. Standalone Lean and Coq proofs cover every initial tape from control 0; the actual repository tape/dense/ZFC adapter remains a separate obligation. Its delivered startup clock is 95,840 versus the primary 95,714, explained by 63 exceptional blocks adding two steps each. This is not a 215-to-214 reduction.

The ternary-register analysis finds zero facts and dead guards, but the inspected pruning candidates raise the source DAG from 202 to 203–205. The finite distinguishing words reject plain state quotients; they do not exclude context-dependent simulations or more general source changes. These negative results should remain attached to their exact families rather than become an impossibility claim.

## Sources 172–173: distinguish CM215, M124 and FM215

Source 172 provides a third CM215 proof, in 24 standalone Lean modules. Its invariant states: at 52 the left cell is 1; at 176 either the current cell is 1 or the left cell is 0; at 156 the right cell is 1. Mapping old 176 to 52 and using one/three-step blocks preserves the entire tape and head at boundaries. The generic positive-stuttering theorem has an empty assumption report in the delivered material. Its standalone machine theorem still needs the repository representation adapter. Do not combine the A/B/E proof counts as three new constructions.

Source 172 also reports exact-equality pilots for shared Lean trees and compact Rocq paths. The joint source-tree representation has 427 shared subtrees. These pilots establish equality at their stated representation boundaries, not a newly rebuilt binary endpoint. Its proposed resolved control-flow semantics and negative row searches remain separate research.

Source 173’s FM215 is closely related to M124 but has different literal bytes. Three patch rows coincide; the replacement 127/1 enters provider 109 in FM215 and 59 in M124. Both providers have the needed read-zero action `0R62`, but their read-one actions differ (`1R42` and `1R72`). Thus the local marker context can justify the provider choice; global equality of the two controls cannot. This is the same kind of marker merger with a different provider, not an additional state saving. Both require their exact table-specific transfer and endpoint bindings.

The full-read [decoder context verifier][contexts] supplies a useful proof design. It expands exactly 4,751 leaves, validates child order, cycles and reachable roles, and checks each internal trace inside its explicit finite window. A passing trace restores the whole window before advancing and never reads the opaque exterior. A Lean frame lemma could then quantify that exterior. The 97 primitive-entry rules bind leaf actions but do **not** prove complete primitive arithmetic or return behavior. Those remain the current site checker’s obligations.

Our independent local census found 281 trace templates and 353 steps when each class is executed once, versus 5,721 local edge-occurrence steps. This agrees with the delivered construction, but it does not predict a matching reduction in the full site checker or kernel workload. All 4,751 source occurrences, their external ports and 6,176 branch cases must remain represented. State/read-bit alone is too small a key: at 69/read 0 the preceding bit distinguishes exits 105 and 104.

Source 173’s [tail-quantifier obstruction][tail] concerns a logical subsystem. In worlds `Nat → D`, quantifier `Q_i` varies every coordinate at least `i`. The model validates the stated classical and native logical rows, equality helper, high-binder vacuity and global generalization. On a two-element domain with strict-order membership, `R(2,3)` can hold while `Q_1 R(2,3)` fails. Falsity `R(0,0)` stays false, and the truth alias is harmless. The delivered Lean development is predicate-level; extension to the numerical decoder is ordinary mathematics. It excludes the nonlogical seed/NK bundles, so it is not a countermodel to the full weakened set-theory calculus. Its retained rejected 214 trial and bounded searches likewise do not prove minimality.

## Lean priorities and current acceptance boundary

The most direct next experiment is Source 168’s normalized certificate over current `WithDecoder`, followed by the small semantic-roundtrip refactor. Decoder frame sharing is promising but requires a generic checked composition theorem before replacing repeated site obligations. The four distinct mechanisms—zero-offset specialization, trailing-zero quotienting, shared tree syntax, and context-dependent decoder traces—must be measured and validated separately.

Nothing in this review changes the chosen primary 215 table, its calibration or the existing endpoint statements. Relative transport proves halting equivalence under its stated initial-control invariant; a standalone transfer becomes a new repository endpoint only after exact representation bindings and the final composition compile. No internal PA derivation, unconditional nonhalting, global state lower bound or newly accepted smaller construction is asserted.

## Appendix: Source 174, separately revised batch 206

The archive `K215_Proof_Simplification_2026-10-21 (2).zip` arrived in `53269bcab1efc0f82d3022645bd7cf0c22d84959`, SHA256 `61a77ed1f34953fe7e8d059f18b9e8a0ccf88f429037fcbf650f011d0349684e`. It has 360 members and 4,255,981 expanded bytes. Upstream `69e6d97fc2ea6da87b718109b1c8614a0927a621` placed it at [k215-simplification-2][G]. A separate supplemental recovery map for Source 174 is still being prepared; the batch 205 recovery claim above covers Sources 168–173 only. Similar report filenames do not identify the same proof: its source lane is ordinary 2,240-entry bisimulation, not Source 168’s 1,426-entry normalized relation.

The revised report and its included source-lane account were read completely, together with the generic 113-line `RMPlainCodec`, final source facade, abstract half-composition lemma and dense endpoint wrapper. The checker parameterizes decoding by an arbitrary function and reuses ordinary `RMBisim.Bisim.halts_iff`; its chosen `decodeAux n n []` removes a fixed fuel cap. Soundness needs no codec-completeness premise. Exact intended decoding remains a concrete data-binding obligation. Phase 5 already implements this generic separation with 512 fuel and the same all-register scope, so this is an independent delivered implementation, not an additional current simplification.

The packet combines that checker with 427 shared tree definitions, partitioned well-formedness and certificate checks, and `allC_of_halves`, which composes abstract checked child facts without reducing the concrete entries again. Its ledger reports 70 locally compiled source modules, including the exact source-to-iterative-DAG theorem. Historical failed large evaluations are retained separately. We did not rerun or audit that full object closure. The remaining prospective value is representation sharing and economical composition, subject to current generators, clients and resource measurements.

Its delivered CM215 theorem reaches the literal imported `KDense215.machine215` through a Core/function-tape bridge. The final ZFC adapter is explicitly supplied but uncompiled. The report’s second marker-fold near miss identifies distinguishable roles 176/211 but lacks retained providers for both required continuations. Its bounded failed helper searches do not close that gap or establish a lower bound. This appendix records the revised proof and its limits independently of the six-source 205 mapping.

[proposals]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/README.md

[A]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/README.md

[B]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-transport/README.md

[C]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/structural/README.md

[D]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc215-simplification/README.md

[E]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc-k215-transport/README.md

[F]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/README.md

[G]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/README.md

[normalized]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/source_normalization/RMNormalizedBisim.lean

[roundtrip]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/structural/calculus/SEMANTIC_ROUNDTRIP.patch

[contexts]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/checks/decoder_contexts.py

[tail]: ../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/research/tail-quantifiers/TailQuantifiers.lean

[map205]: data/intake205-placement.json

[recovery205]: data/intake205-recovery-control.json
