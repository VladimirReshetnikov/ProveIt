# Height-preserving cut-free conjunction inversion

`ParsonsSelection` proves the actual inversion needed in the Joosten
cut-free induction-axiom case, for Foundation's one-sided list calculus and
an arbitrary language. Given any cut-free derivation of `(A ⋏ B) :: Γ`, each
of `A :: Γ` and `B :: Γ` has a cut-free derivation of no greater height.
The three-conjunct corollary gives all three matrix premises at the same
height bound. The more general theorem simultaneously replaces any selected
occurrences, including duplicates, by either conjunct.

The induction on the actual cut-free derivation handles every constructor.
The contraction case uses `pullback` to select a compatible premise context
and retain its inclusion in the chosen conclusion context; the universal
case shifts every selected formula to preserve the eigenvariable discipline.
No excluded axiom, theory-specific property, or hypothesis of logical
provability is assumed.

Both new source files were snapshotted before compilation and built twice in
fresh private outputs under Lean 4.32 `-M6000 -j1 -DElab.async=false`. Both
objects and complete logs matched. Seven axiom reports use only `propext`
and `Quot.sound`; there were no warnings. The [17-file replay manifest](parsons-selection-replay/FILES.json)
SHA-256 is `36b865b4974c663c13cd73a02094dc7bbab7c474baa8d61c371c49c4b51582c1`.
The first left-only scratch proof is retained. Extending it to both conjuncts
initially failed because the replacement formula was not generalized in the
universal-rule induction; generalizing it fixed the issue, after which both
final builds passed. The exploratory command's console output was not saved.

The builds selected the existing Foundation/Mathlib object directories; they
are a stated inherited dependency boundary, not a fresh source-closure audit.
The theorem establishes the logical inversion step alone. Converting the
induction-axiom case to an induction-rule derivation and proving the PRA
witnessing theorem remain open.
