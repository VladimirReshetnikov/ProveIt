# A smaller proof of the context-return variant

The current committed context-return table has SHA256 da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627. It differs in exactly five rows from the formally certified native K215 table9683d6ed…. Its source is unchanged. Current committed shallow/context bytes match the older packet used for these independent checks.

## Main recommendation

Do not rebuild the6,176 primitive-site certificates or replay a new initialization proof for this variant. Prove a generic finite-history patch-transport theorem once and instantiate it with six tiny whole-tape blocks. The existing exact K215 endpoint theorem then transports directly. This is a genuinely smaller INCREMENTAL proof of this alternative, not a replacement that makes the original base endpoint unnecessary.

The finite checker is check_patch.py, authored locally and independent of the repository verifier. It reads only tables and certificate data. Run it with Python standard library. It checks:

1. Identical complete working-state domains, exactly five modified transition rows, same start0 and separate halt254.
2. Six block guards cover all modified rows. Every block is replayed exactly on both literal tables; all reads lie inside its explicitly specified finite window. The two endpoints have identical state, head and every window cell. Arbitrary exterior tape is untouched.
3. Both durations are positive. No strict block interior is halting or uses a modified row. The six pairs use28 total literal transitions.
4. Every graph history of the required length ending in a changed-row entry implies a block guard, after accounting for the latest write at each relative cell and the currently read symbol. Histories are an overapproximation; impossible earlier read/write combinations can remain. One path whose latest write contradicts the entry read is safely discarded.
5. Start0 cannot reach a changed entry too early for its history lemma, regardless of tape contents.

Only the OLD table's history obligations are necessary: five two-edge paths into13 (one contradicts entry read1), and four immediate incoming edges for27,83,156,198. Thus nine history paths, eight compatible cases. Checking both tables would produce17 paths and is unnecessary; the older both-sided receipt is retained only as extra evidence.

## Generic theorem and proof

Let A and B be deterministic Turing machines with the same configuration representation, working states, halt state and initial state. Suppose the checks above succeed, with history coverage for configurations reachable in A from the initial state on arbitrary initial tape.

At a synchronized boundary the machines have exactly the same full configuration. If it is halted, both halt. If its next row is unchanged, take one common step. Otherwise A's reachable-history lemma selects a valid block; run the positively many certified A steps and B steps. Their complete endpoints agree. Each endpoint is again reachable in A, so its history lemma is available without an invariant about B's history.

Iterate these matched boundary blocks. Each block is finite and positive on both sides, and no halt lies strictly inside it. Consequently either both executions halt at a common boundary or both continue forever. Equivalently, prove each finite-halting implication by induction on its remaining concrete transition count, subtracting the positive block duration; an alleged halt strictly inside a certified block contradicts the checked nonhalting interior. This is positive stuttering equivalence, not step-for-step equality.

Therefore for EVERY initial tape tau and head position h:

    Halt(A, state0, h, tau) iff Halt(B, state0, h, tau).

The history proof uses no blank-tape fact. Blank startup equivalence is a corollary, so a separate95,740-step initializer certificate is not needed for theorem transport. Source semantics, numerical-calculus calibration and the existing K215 runtime proof are reused unchanged. Neither an already-halted strict interior nor zero-duration stuttering is allowed.

This theorem/checker design has not been compiled in Lean or Rocq. The checker supplies explicit finite premises, and the argument above explains their sufficiency. Do not describe it as a newly kernel-checked endpoint.

## Comparison with shallow and DR215

Fresh owned finite-window decoder checks give:
- Certified K215, context215 and shallow215:281 templates,234 product states,468 product edges,97 exposed leaf contexts each.
- DR215:281 templates,236 product states,472 edges,95 leaf contexts. Its ST215 parent previously had235 states/470 edges/95 leaf contexts.

Thus reducing maximum source depth from47 to46 does not simplify this decoder proof interface. The shallow variant needs a source-reassociation transport in addition to physical checks. DR215 is a meaningful source alternative but is not physically simpler by this metric.

A useful incremental method for DR215 is a symbolic-evaluator dependency theorem: if two tables agree on every row read by a previously verified symbolic execution and the same box-oracle theorems remain valid, that execution and its whole-tape endpoint theorem transport unchanged. This must include dynamic lookups in scan/peel rules, branch assumptions, and oracle proof footprints.

An owned transcription of the inspected Lean rules finds that DR's two changed rows affect139 guarded executions, although only four source operands change. Those139 changed executions pass;6,012 of6,151 have disjoint direct evaluator footprints. It would be UNSOUND to recheck only four operands/eight branches: unchanged source sites also use the shared decoder rows. Reuse of the6,012 proofs still requires a formal dependency theorem and a bound showing the corresponding BoxLemmas are preserved. The table's two modified decoder rows do not appear in the prior engine-only footprint evidence, but this observation alone is not a newly compiled oracle theorem.

## Attribution and comparison with newly received transport archives

The incoming FM215 and M124 archives already describe old-run-only positive stuttering, arbitrary-initial-tape equivalence at control0, and reuse of the baseline endpoint without new runtime or startup proofs. The M124 comparison explicitly identifies the context-return alternative as a larger multi-block case. Therefore the present result is an independently checked instantiation and obligation count, NOT a claim to invent generic stuttering, one-sided-history transport, or all-tape strengthening.

FM215/M124 need two incoming-marker facts and two three-step blocks, fewer obligations than the context-return certificate's six blocks and nine incoming graph histories. Subject to verifying their table binding and reported formal compilation, they have smaller local proof obligations, but this alone does not establish the least remaining endpoint-integration work. The context-return checker remains a useful generic multi-block certificate test and independently checks the committed table. Incoming compiler logs were not executed or independently reproduced by this checker.

## Final recommendation: attachment completeness outweighs clause count

CM215 currently has the least remaining work to inherit the maintained Lean K215 endpoint. The archive named K215_Proof_Simplification_2026-10-21 (2) contains CM215Core.blank_halts_iff_primary in the repository's actual Machine215/KDenseBridge.BlankHalts semantics. Its archived compilation records cover the exact430-row compatibility checks, the CoreNativeBridge representation theorem and this exact-machine equivalence, with reported axioms propext and Quot.sound. CM215ZFCAdapter.lean already imports KEndpoint215 and composes blank_halts_iff_zfc_refutation, but explicitly was not included in the fresh full-endpoint build. Another CM transport archive independently records compiled CM215Dense/core bridge and likewise provides an uncompiled final integration wrapper.

Minimal remaining CM obligation: place/rebuild the supplied adapter against the maintained endpoint dependency closure, verify exact module/table bindings and inspect its final assumptions. No new representation theorem or runtime-site proof is indicated by these records. This is the closest supplied adapter, not a claim that the complete alternative ZFC endpoint has already been rebuilt.

FM215 has a shorter local proof and an archived successful Lean all_tapes_halts_iff theorem, but its theorem uses standalone integer/function-tape configurations. The supplied FM proof does not contain a compiled adapter to the repository's Machine215/KDenseBridge.BlankHalts endpoint. Minimal remaining FM obligations: instantiate or adapt a generic representation bridge, bind both exact literal tables and start/halt labels, then compose and compile the final maintained endpoint. The existing generic CM bridge may be reusable, but reuse itself must be checked.

M124 similarly has standalone all-tape exact-table equivalence in both Lean and Rocq. The Rocq receipt reports closed assumptions and successful coqchk; the Lean receipt lists propext, Classical.choice and Quot.sound. Both explicitly exclude integration with the upstream ZFC endpoint model. Minimal remaining M124 obligations: on Lean, the same exact table/model bridge plus endpoint composition; on Rocq, a stream-zipper/BusyCoq-to-integer-tape bridge with the native301→102,302→120,254→230 map, OR port the short local marker proof directly into the existing BusyCoq semantics, then compose with CorrectDense215.

Therefore distinguish two answers: FM/M124 have the simpler local marker argument; CM has the most complete supplied compiled attachment and is presently the best near-term endpoint-integration choice. None removes the inherited K215 logical/calculus dependency closure. Archived records were inspected, not recompiled by this audit. ADAPTER_AUDIT.json pins the precise sources and records used.
