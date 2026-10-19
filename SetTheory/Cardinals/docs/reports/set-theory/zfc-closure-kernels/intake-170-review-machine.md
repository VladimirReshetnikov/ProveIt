# Independent source review of the 240-state construction

The ordinary source-rotation and local-fold arguments are coherent. The delivered baseline table is byte-identical to the maintained `candidate-fold241/zfc_fold241_old.tm`. The final machine has 240 working states, 480 rows, and a separate halt state. No mathematical blocker was found in the reviewed proof. This is a source review plus my own literal and source-graph checks; I did not run a delivered program, machine simulator, runtime checker, Lean compiler, or checksum-manifest validator.

## Exact change and why it combines

Starting from the existing 241-state table, the intermediate machine changes only `142/0: 0R37 → 0R72` and `142/1: 1R72 → 1R17`. It implements a new source program, retaining all 241 labels. The final fold deletes 90 and changes `72/0: 0R57 → 0L144`, `72/1: 0R64 → 1L36`, and `79/1: 1R90 → 1R72`. All other 475 retained rows are identical to the maintained baseline. I checked every row, the complete target set, and the canonical bijection (start0, dispatcher84, halt240).

This legitimately retains the preceding 27→15 and 39→17 savings: they are already present in the exact input table and the new exceptional paths use their actual resulting rows. It is not an additional same-source fold on the unrotated table. In particular, old `142/1` entered72 with left bit1; the new source rotation removes that entry and is essential to the stronger invariant. Existing old-side Fold242/Fold241 invariant theorems should not be silently applied to the newly rotated table or to the already-merged control17.

## Source equivalence

At each of four incomparable prefixes, replace `Node(Node(D6,Node(I5,C2)),I5)` by `Node(I5,Node(D6,C2))`. For arbitrary natural register files, both terminate with `R5 := old R5 + old R6 + 1`, `R6 := 0`, every other coordinate unchanged, in exactly `3·old R6+2` source instructions. The zero case uses two instructions. The positive case uses one increment, one successful decrement and one continue, returning with `(R5+1,R6−1)`. Distinct coordinates justify the reordered operations; no execution bound substitutes for this induction.

My own literal source-graph reconstruction checks all 8,370 outside guarded edges, all four internal macro graphs and both whole leaf lists. Outside leaves retain their instructions. Outside edges enter only paired macro entries, never their interiors, and the corresponding exits agree. Initial and unique halt leaves are unchanged. Thus complete-register-file macro replacement gives both halting directions. Counts are 6,459→6,455 leaves and 8,390→8,386 guards, maximum depth51. The source statement is not an all-tape binary equivalence between original241 and rotated241.

There is a particularly small Lean route: the delivered new leaf list is exactly the expansion of `ProgramRotation244.program` with **only DAG row169 replaced by `(inc5,node5)`**. Existing row5 is already `(decnz6,cont2)`. Old rows169/45/44 are the original transfer-plus-one shape; rows44/45 must remain unchanged because they are shared elsewhere. The checked `RMDagLoopRotation.run_iff` applies with old nodes169/45/44, new nodes169/5, source6 and destination5. The checked context-substitution theorem can use `safe := True`, since only the macro entry row changes. This avoids re-proving thousands of source edges in Lean. A new exact program/WF/path bridge is still required; this review did not compile it.

## Local binary fold and complete tapes

On the rotated241 machine, controls55,142,90 imply a left-hand1; control72 implies two-left1 and left0. The complete incoming inventories prove preservation: 37/1→55,119/1→142,79/1→90 write1 and move right;55/0 and142/0→72 write0 and move right, and their predecessor invariant supplies the additional1. At start95 every condition is vacuous for every head and tape.

Map90→72 and keep other controls fixed. The exceptional old rows72/0,72/1,90/0,90/1 match respectively9,3,3,3 new steps. I read all four calculations and independently bound all16 distinct row facts used by them to the final table. The nine-step path is `72,144,47,15,32,46,17,106,93,57`; it preserves the known local pattern100. Other cases reproduce the required old write and destination. Every exceptional read/write lies between the initial head−2 and head; all outside cells remain unchanged. No exceptional path passes through halt. Every ordinary action commutes with the state map (checked for all ordinary rows).

The positive-block induction therefore yields halting equivalence from95 on arbitrary complete binary tapes and heads, with `N(n)=n+8V(72,0)+2(V(72,1)+V(90,0)+V(90,1))` and `n≤N(n)≤9n`. Existing `PositiveBlockBisimulation` can formalize the finite-support Core specialization sufficient for blank input. The delivered 7,640-window enumeration was read as code, not executed by me; its footprint assertions make the advertised extension to arbitrary exterior tape appropriate.

## Calibration and evidence limits

The archive reports rotated startup408,941, final startup409,691, and a final complete runtime certificate of8,386 guards,2,322,575 rules, all480 rows, minimum duration13. The reported exceptional startup visits74,37,18,24 yield exactly750 extra steps. The final full frame has logical registers `(3,0,0,0,3,0,0,0,0)`,167 **value-one** spare blocks, head−5, marker−6, header176 and351 one-cells. These remain delivered evidence, not fresh executions by this reviewer.

The runtime engine differs from its pinned predecessor only in source count, source SHA and receipt-field name; its induction/transition rules are unchanged. A rotated-table runtime theorem plus exact rotated blank frame and the new source theorem are still needed to calibrate the intermediate binary machine. Alternatively one may prove runtime and startup directly for the final240 machine. Existing Rotation244 coverage does not automatically transport through the row142 changes: instruction endpoints alone do not exclude visits to changed intermediate controls. The incoming report correctly keeps this binary bridge separate from its source theorem and the local72/90 fold.

The ordinary ZFC consistency interpretation is conditional on the inherited exact source/calculus calibration. The report does not supply a newly compiled complete240-state Lean/Rocq endpoint, internal PA theorem, absolute consistency proof, unconditional nonhalting, minimality, or two-sided independence from bare consistency.

## Additional useful research and attribution

The rational-cut model `(Q≥0,<,=)` argument is sound: explicit affine order automorphisms give every weak-Collection instance, while the empty-output instance refutes GIC support; CP and the listed elementary axioms have the described witnesses. The proof of `GIC ↔ weak Collection + full Separation` uses nonempty structures and native equality. The exact orbit evaluator is an independent rejection tool, not a new machine saving. Opening's separate theory/driver review records two reusable-tool validation limitations that do not affect the supplied corpus; this review makes no claim of arbitrary-input tool validation.

Attribution distinguishes the inherited Mira-Cult/Ketchersid/Wade/ProveIt chain from this concrete source142-plus-fold90 construction. It does not claim invention of transfer rotation or predecessor-bit sharing. Negative searches are explicitly restricted certificate families, not lower bounds.

The own reviewer initially represented the halt leaf's unused payload as0 instead of the delivered JSON null. That metadata-only draft stopped at the exact DAG/list equality before a receipt was written. Its bytes are retained under `history/reviewer-draft1-halt-serialization/`; the sole normalization correction does not alter source, tables, proofs or delivered evidence. The final script completed49,749 static comparisons.
