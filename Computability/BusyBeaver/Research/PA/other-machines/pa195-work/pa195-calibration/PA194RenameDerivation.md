# Model-internal PA derivations are closed under expanded renaming

`PA194RenameDerivation.lean` proves that in every nonempty candidate-PRA model
with equality and an IΣ₁ arithmetic reduct, if an internal finite formula
context `Γ` is internally derivable in Foundation's PA calculus, then its
image under any member of `PA194ExpandedRename` is internally derivable in PA.
The context, derivation code, and all four map parameters may be nonstandard.
The theorem asserts existence of an internal derivation; it does not construct
a fixed primitive-recursive transformation of derivation codes.

The proof applies Foundation's IΣ₁ induction over internal derivations to a
bounded Σ₁ invariant that quantifies over all map parameters up to `b` and
requires `prefix + derivationCode ≤ b` and `offset + derivationCode ≤ b`.
Each recursive child has a strictly smaller code, supplying the extra unit
needed when universal introduction increases the protected prefix or a shift
branch increases the offset. The other parameters decrease or stay fixed.
All ten rule cases use the separately checked conditional preservation
lemmas. For any desired initial parameters and code `d`, the proof takes
`b = (prefix+d) + (offset+d) + exception + flag`, discharging the bounds.
No positive-offset or injectivity assumption is needed for this derivability
result.

Lean reports `propext`, `Classical.choice`, and `Quot.sound` for the printed
theorem dependencies, with no `sorryAx`. The theorem is model-uniform under
the displayed IΣ₁ hypothesis. It is not yet an object-theory iPRA theorem or
a PA194 consistency implication: identifying the initial formula renamer
with `free (close label 0 φ)` and connecting the result to the source proof
compiler remain separate obligations.

Run `check-rename-derivation.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent suffix replay recompiled this final module against the author's
retained ordered dependency overlays; the reported axioms did not include
`sorryAx`. An independent complete fresh dependency replay also passed with the audited
overlays and no `sorryAx` in the checked theorem dependencies.
