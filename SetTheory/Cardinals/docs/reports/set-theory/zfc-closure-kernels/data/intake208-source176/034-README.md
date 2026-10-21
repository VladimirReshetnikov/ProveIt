# Recent-commit runtime proof simplification

The inputs correspond to main commit53269bcab1efc0f82d3022645bd7cf0c22d84959. The context-return and shallow bytes were independently matched to that intake. The literal tables and source files are pinned in pins.json and the file manifest. Everything executed here is owned checking code, not received repository scripts.

Recommended first read: PROOF_DESIGN.md. The main independently checked application is a one-sided-history patch theorem transporting the existing K215 endpoint to context215, avoiding a new source proof,6,176 site proofs and a separate initializer proof. Six short blocks and nine old-table history paths suffice. The all-initial-tapes strengthening and elimination of new-table history obligations are independently checked simplifications of the supplied block argument, not a claim to have invented generic stuttering equivalence.

Run:
- python check_patch.py
- python test_patch.py
- python check_decoder.py
- python check_dr_delta.py

The first three finish quickly. The DR dependency census takes several seconds and records an exact direct evaluator footprint. All use only the Python standard library.

check_decoder.py checks every local template with opaque exterior, and the entire source-node/physical-state/two-bit-history coverage product. It does not discharge generic leaf-return obligations. check_dr_delta.py assumes the corresponding BoxLemmas, following the previously inspected Lean symbolic rules; formal reuse of unchanged oracle theorems requires their dependency footprint separately. No new Lean/Rocq compilation or measured proof-assistant speedup is claimed.

Results: context215 and shallow215 have the SAME decoder interface counts as certified K215; DR215 has one more product state than ST215. These alternative tables do not offer a smaller standalone physical-runtime theorem by that metric. The context variant nevertheless has an exceptionally small incremental transport proof. DR's two modified rows affect139 guarded executions, not merely the four changed source operands, so direct reuse should recheck139 and transport6,012 after proving the dependency theorem.

## Attribution and comparison with newly received transport archives

The incoming FM215 and M124 archives already describe old-run-only positive stuttering, arbitrary-initial-tape equivalence at control0, and reuse of the baseline endpoint without new runtime or startup proofs. The M124 comparison explicitly identifies the context-return alternative as a larger multi-block case. Therefore the present result is an independently checked instantiation and obligation count, NOT a claim to invent generic stuttering, one-sided-history transport, or all-tape strengthening.

FM215/M124 need two incoming-marker facts and two three-step blocks, fewer obligations than the context-return certificate's six blocks and nine incoming graph histories. Subject to verifying their table binding and reported formal compilation, they have smaller local proof obligations, but this alone does not establish the least remaining endpoint-integration work. The context-return checker remains a useful generic multi-block certificate test and independently checks the committed table. Incoming compiler logs were not executed or independently reproduced by this checker.

## Final recommendation: attachment completeness outweighs clause count

CM215 currently has the least remaining work to inherit the maintained Lean K215 endpoint. The archive named K215_Proof_Simplification_2026-10-21 (2) contains CM215Core.blank_halts_iff_primary in the repository's actual Machine215/KDenseBridge.BlankHalts semantics. Its archived compilation records cover the exact430-row compatibility checks, the CoreNativeBridge representation theorem and this exact-machine equivalence, with reported axioms propext and Quot.sound. CM215ZFCAdapter.lean already imports KEndpoint215 and composes blank_halts_iff_zfc_refutation, but explicitly was not included in the fresh full-endpoint build. Another CM transport archive independently records compiled CM215Dense/core bridge and likewise provides an uncompiled final integration wrapper.

Minimal remaining CM obligation: place/rebuild the supplied adapter against the maintained endpoint dependency closure, verify exact module/table bindings and inspect its final assumptions. No new representation theorem or runtime-site proof is indicated by these records. This is the closest supplied adapter, not a claim that the complete alternative ZFC endpoint has already been rebuilt.

FM215 has a shorter local proof and an archived successful Lean all_tapes_halts_iff theorem, but its theorem uses standalone integer/function-tape configurations. The supplied FM proof does not contain a compiled adapter to the repository's Machine215/KDenseBridge.BlankHalts endpoint. Minimal remaining FM obligations: instantiate or adapt a generic representation bridge, bind both exact literal tables and start/halt labels, then compose and compile the final maintained endpoint. The existing generic CM bridge may be reusable, but reuse itself must be checked.

M124 similarly has standalone all-tape exact-table equivalence in both Lean and Rocq. The Rocq receipt reports closed assumptions and successful coqchk; the Lean receipt lists propext, Classical.choice and Quot.sound. Both explicitly exclude integration with the upstream ZFC endpoint model. Minimal remaining M124 obligations: on Lean, the same exact table/model bridge plus endpoint composition; on Rocq, a stream-zipper/BusyCoq-to-integer-tape bridge with the native301→102,302→120,254→230 map, OR port the short local marker proof directly into the existing BusyCoq semantics, then compose with CorrectDense215.

Therefore distinguish two answers: FM/M124 have the simpler local marker argument; CM has the most complete supplied compiled attachment and is presently the best near-term endpoint-integration choice. None removes the inherited K215 logical/calculus dependency closure. Archived records were inspected, not recompiled by this audit. ADAPTER_AUDIT.json pins the precise sources and records used.
