# Independent review of the dense bridge and Rocq mirror theorem

Date: 2026-10-21. This review examines the source of `OffsetMirror.v`, `CoreNativeBridge.lean`, and `CM215Core.lean`, together with the definitions imported from `RM.v`, `Bisim230.v`, `OffsetBisim230.v`, `BusyBeaver.Core`, `KDense215`, and `KDenseBridge`. It does not launch another compiler. Reviewed new-file hashes and exact table-comparison results are in `dense-review.json`.

## Conclusion

**No mathematical correctness defect was found.** The added dense bridge closes the native/dense semantics gap identified in the earlier review of the standalone transfer. The current conclusion is a transfer theorem between the actual dense machines in the unchanged repository's machine semantics. This review does **not** claim that a full CM215/ZFC adapter or the inherited ZFC dependency closure was rebuilt.

## Rocq: `OffsetMirror.v`

The theorem concerns the actual imported offset-certificate checker. It does not introduce a replacement checker whose soundness would need to be reproved.

The defining relation is `R1(i) = R2(i) + delta(z,i)` in the integers. Swapping register files therefore negates the offset. The increment-count condition

`delta(z,i) + count(l1,i) = count(l2,i) + delta(z',i)`

is equivalent to the mirrored condition with `l1,l2` swapped and both offsets negated. `counts_ok_mirror` derives precisely this identity, including registers outside the displayed count-support list through the existing `counts_ok_sound` lemma.

Certificate indices `j,k` remain unchanged. They identify the nonzero and zero branches of the same tested register on both sides, not left-versus-right machine identities. Swapping programs therefore swaps addresses and negates offsets while preserving those branch indices. The zero-offset test at each tested register remains true after negation. Halt/halt entries are symmetric directly.

`ocheck_mirror` derives the reverse Boolean check from the forward check, so `ocheck_iff_of_forward` legitimately removes the second certificate-check premise from the existing soundness endpoint. It quantifies all initial natural-valued register files at the empty instruction pointer. No nonnegativity assumption about the integer offset is smuggled in; the runtime register files remain natural-valued and the relation embeds them into integers.

The imported `rm_halts` requires a finite run ending at an actual `EHalt` leaf. An invalid walk, fuel failure, or stuck instruction returning `None` is not counted as halting. The finite segment fuel is an acceptance limit for certificates, not a bound on program runs. No extra axiom or admitted statement appears in the new source or the inspected checker dependencies.

## Lean: `CoreNativeBridge.lean`

The generic bridge represents a finite-support repository tape by its full read function on `Int`. The `read_write` lemma commutes each finite-list write with the full-function update, including tapes with duplicate list entries. Only observed bits matter; no equality between different list representations is assumed.

`Compatible` compares every dense working-state transition and both input symbols. It preserves the written bit, move direction, and mapped next label. Dense `none` is mapped to the designated native halt. `embed_step` then preserves one exact transition, including head movement and the entire read function. Halted configurations are fixed in both semantics.

`halt_embed` is sound even without a separate injectivity assumption for the label map: each dense working state is required to have a `some` native row, while the mapped dense halt has `none`. The row and halt premises already prevent confusion between working labels and halt. `embed_run` is a synchronous induction, and `blank_iff` uses the actual blank initial state, head 0, and all-false tape.

## Lean: `CM215Core.lean`

An independent parser compared all 430 literal rows of `rowsCM` with the released `marker215.tm`, and all 430 rows of the imported `KDense215.rows215` with the released `k215.tm`. Both comparisons were exact.

The new `nativeLabels` list contains exactly 215 distinct labels, begins with 0, and omits 254. Relabeling all dense transitions through this list, with dense halt 215 sent to 254, reproduces the corresponding pinned native tables exactly. The default value in `nativeLabels.getD` is unreachable for `Fin 215`; both row lists also have exactly 215 entries. Hence neither fallback creates an unexamined behavior. The standalone native table closure facts independently exclude the unused labels of `Fin 303` from reachable runs.

The composition

`CM dense halting ↔ CM native halting ↔ primary native halting ↔ primary dense halting`

has the correct orientation in `blank_halts_iff_primary`. It proves equivalence of the actual blank halting propositions under the repository's existing `Machine 215` semantics. No additional register, source-calculus, or ZFC hypothesis enters this transfer.

## Remaining integration boundary

The new dense theorem can be composed with the existing primary `KEndpoint215` theorem. The resulting source adapter would be short. A full build of that adapter imports the inherited numerical-calculus/ZFC proof closure; neither the independently reviewed sources nor this review should be described as having freshly rebuilt that closure unless the final build evidence establishes it.
