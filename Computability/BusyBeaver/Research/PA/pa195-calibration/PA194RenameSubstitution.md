# Internal renaming, substitution, and eigenvariables

`PA194RenameSubstitution.lean` proves that internal free-label renaming
commutes with Foundation's bound-variable substitution on terms and formulas,
provided the internal input formula or term and substitution vector are
well formed at the stated model-valued depths. The substitution vector itself
is renamed componentwise. The proof establishes compatibility with bound
shift and `qVec` under quantifiers. All input syntax, depths, vectors, and map
parameters may be nonstandard.

For an internally well-formed depth-one formula `φ`, it also proves

```
rename(p, free φ) = free (rename(q, φ))
```

whenever the free-label map satisfies `f p 0 = 0` and
`f p (x+1) = f q x+1` for every model value `x`. The final theorem supplies
these hypotheses for the expanded family with the protected prefix increased
by one on the left. This is the formula-level eigenvariable identity needed
for Foundation's `allIntro` premise.

The theorems hold in every nonempty candidate-PRA model with equality and an
IΣ₁ arithmetic reduct. Generic statements require a supplied Σ₁ graph that
correctly represents the free-label map at every model value; the expanded
family's fixed graph has that correctness proved. Lean reports `propext`,
`Classical.choice`, and `Quot.sound` for printed dependencies, with no `sorryAx`.
No semantic truth predicate is used.

The identities do not yet map finite formula contexts, produce an internal
proof transformer, or establish an iPRA consistency implication. Those remain
open.

Run `check-rename-substitution.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local prerequisite chain and finding no `sorryAx` in the displayed theorem
axioms.
