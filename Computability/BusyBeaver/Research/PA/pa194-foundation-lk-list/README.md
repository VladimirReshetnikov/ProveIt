# List-based computable Foundation LK compiler for PA194

`findPreimage` replaces the previous multiset traversal's data-level
`Classical.choose` with decidable search of the original Foundation sequent
list; its printed axiom dependencies are `[propext, Quot.sound]`.
`refutesAllList` uses that search to handle universal introduction.
`compileFoundationLKList` and `compileFoundationContextList` adapt the
checked current-Foundation LK compiler to that list-based universal case.
They are accepted as ordinary computable Lean `def`s, without a
`noncomputable` section, explicit `Quotient.out` or `Classical.choose`, or
`sorryAx`. Their printed axiom dependencies remain `[propext,
Classical.choice, Quot.sound]` through proof dependencies.

The theorems preserve the original compiler's explicit label/freshness and
`listFoundationBudget` assumptions. Lean-level computability is not a proof
that the compiler on encoded proofs is primitive recursive, that a suitable
bound is provable in IΣ₁, or that its correctness holds for nonstandard
model codes. A coded syntax and proof transformation, complexity bound and
internal correctness proof remain necessary before applying the IΣ₁ model
transfer to a machine reduction. PA-refutation translation and the machine
biconditional also remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-lk-list/check.sh`.
The script rebuilds the nested Foundation-LK prerequisites in tmpfs, checks
source pins and rejects `sorryAx` in printed axiom dependencies. All three
new modules passed an ordered fresh overlay replay; the full standalone
nested replay has not yet completed.
