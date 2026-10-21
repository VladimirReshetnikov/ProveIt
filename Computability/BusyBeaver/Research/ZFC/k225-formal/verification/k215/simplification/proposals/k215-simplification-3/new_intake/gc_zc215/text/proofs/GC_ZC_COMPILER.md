# Command-tag generalization plus zero-credit enumeration

Status: completed ordinary calibration. All6,177 universal primitive guards and all430 rows passed; sparse and dense blank startup agree after117,004 transitions. This is not a newly compiled Lean/Rocq endpoint.

Use ZC's four-command interface DROP, NIP, MP and AX. Change only AX's ninth stack head from Q_D(oldH) to Q_C(oldH). The first parameter-load macro in AX changes from a preserving D load to the existing preserving C load. Every other AX arithmetic operation, parameter, gated bundle, stack head and cleanup operation is literal. The zero-debt scheduler proof counts DROP and NIP only, assigns AX and MP zero credit, and is therefore unchanged.

The original four-command strong compiler still applies to truth, seven retained rows, the dominated L row, the gated bundle and MP. Its arguments either use C=D already or discard the generalization head using only its tag2, hence the fact that it is never1. They do not require the old binder value in discarded heads.

Generalization now has the shorter block:

    B_X; DROP; NIP; AX(i;0,0); NIP^9; DROP; NIP; NIP.

Indeed B_X returns (X,w,0,0); DROP gives (0,[X;w],0,0); NIP gives (0,w,0,X). AX then emits Q_i(X) in position9 and saved0 in position10. Its top G may now be enabled because A=0,B=X,C=i; this is harmless. Every gated top is zero or implication-coded and therefore never1. NIP^9 loads Q_i(X) into cache, DROP makes it the top and saves G, and two NIPs discard G and saved0. The final tuple is (Q_i(X),w,0,0), or an earlier permitted halt. The old J(i) command is removed even when i=0, so no numerical alias special case is needed in this block.

The lower-tag DROP/NIP injection gives zero initial protected debt from N=1,L=0,T=H=0 with arbitrary opaque stack tail, exactly as in ZC. Shorter generalization does not alter command arities, ordering or scheduler. Exhaustive enumeration from raw0 reaches the reset-leading compiled refutation, so cofinal-padding arithmetic can be omitted. This is a simpler generalization and resource proof than the ST/FT three-command protected-debt approach, though the already formally certified K215 all-theorem seed may still be cheaper to maintain than either alternative.

## Construction and separately verified obligations

The literal first-load replacement in ZC yields203 source DAG nodes and a216-state allocation, adding state303=(0R154,1R86). The GC215 conditional decoder recipe has the same new role, numbered310, and merges it with129 using129/1=1L216. Applying that exact recipe to this composed allocation gives215 states. The construction count alone would not certify this merge: marker-origin hypotheses depend on source context, not merely matching transition rows. The completed portable audit below proves those hypotheses from all incoming edges, and the separate universal runtime and startup checks discharge the remaining binary obligations.

Final files: gc_zc.sites.json and gc_zc215_start74.native.tm. Construction records: GC_ZC_PRICE.json and GC_ZC_MERGE.json; the latter records the preserved raw replay input before header correction. All received inputs were read as inert data; no received script was executed. The shared owned allocator created the preliminary216 table, and a literal owned transformation applied the conditional merge.


## Completed calibration and exact binary scopes

The preserved raw runtime input gc_zc215.native.tm has SHA256 da889c32513713e131fa97247247feb6a85d5f3ad29d38221425025b0ec550de. Its serializer header incorrectly says start0, so it is not the final start-declaring artifact. The verified actual native start is74. The corrected gc_zc215_start74.native.tm has SHA2564122c18a347028ee6643428b70a8d5c81218d4937d672be3626981d7b50bf503. HEADER_TRANSPORT.json establishes byte-for-byte equality of all430 transition rows; only the comment header changes. No replay input was overwritten.

The independent universal runtime replay covers6,177 guarded cases, arbitrary natural registers and gap, arbitrary nonempty finite spare lists, and zero exterior. All430 rows are covered. The native74 blank execution and independent dense execution both reach the exact source root after117,004 transitions with logical registers N=1,T=0,W=5,A=D=H=X=Y=L=0, head-4 and gap20. The physical spare list is mixed but permitted by the all-natural runtime domain. Thus the actual seed is precisely the opaque-tail seed of the ZC tag-lowering theorem; no synthetic AX prefix or initial positive credit is used.

The portable verify_composition.py recomputes literal source equality except operands46/51, all unchanged primitive addresses/control-flow kinds, deterministic table reconstruction, and the conditional merge. Its merge proof is simpler than a dynamic history invariant: in the unmerged216 table the only incoming129 edge writes1 then moves right; the only incoming303 edge writes0 then moves right. Hence predecessor markers are forced on every entry. Four finite local traces prove identical tape and head endpoints for both read symbols. This establishes the merge for all executions, conditional only on the exact reconstructed predecessor table, not on a bounded corpus.

For soundness, the unchanged tag-lowering injection associates every NIP with a distinct earlier DROP by lowering its one-field command tag. This guarantees an explicit theorem head before every pop, regardless of the opaque tail5 and without counting AX output. The changed ninth AX head is safe by unrestricted theorem-only numerical GEN. Hence any halt is a native refutation. For completeness, the strong compiler above and the inherited other blocks produce a finite refutation word from arbitrary numerical top/stack after a resetting AX. Exact exhaustive raw-code enumeration from0 reaches this word, and every prior nonhalting candidate drains by strict decrease of the positive residual. Thus a native refutation implies a halt. The inherited numerical-calculus calibration identifies these native refutations with ZFC inconsistency.

Therefore the corrected exact215-state table, from its declared start74 on a blank tape, halts if and only if ZFC is inconsistent, under the same explicitly inherited calibration as the parent candidates. Its dense canonical relabeling has start0. It is not a214-state construction. Compared with GC215 it replaces quantitative protected-debt reasoning and the AX startup bridge with zero-debt tag lowering and a direct root seed. Compared with ZC215 it removes the counter-loading J(i) step from generalization. Compared with the already certified K215, it adds a new protected-tail and physical-merge formalization, so it is not claimed to minimize total proof-assistant migration effort.
