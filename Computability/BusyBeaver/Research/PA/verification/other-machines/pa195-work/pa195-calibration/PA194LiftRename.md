# Lifted free-label renaming

`PA194LiftRename.lean` constructs an explicit candidate-PRA `Code 3` for the
index map

```
g(k,a,x) = x       if x < k
           k       if x = a + k
           x + 1   otherwise.
```

The arguments are the protected-prefix length `k`, the selected source label
`a`, and the variable index `x`. At `k = 0`, the map sends `a` to zero and
sends every other index to its successor. The theorem `modelCode` proves the
code computes this map in every nonempty candidate-PRA model with equality
interpreted as equality, for all model elements including nonstandard values.
No IΣ₁ assumption or projection-code certificate is used.

The file proves the map is injective for every `k` and `a`, and proves the
lift equations `g(k+1,a,0) = 0` and
`g(k+1,a,x+1) = g(k,a,x)+1`. These are the variable-level equations needed
when passing the renaming through an eigenvariable binder. The printed Lean
axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorryAx`.

This is a finite index-renaming code and model-uniform arithmetic about it. It
does not yet lift the renaming through arbitrary internal formulas or
transform internal PA derivations, and it does not prove the source
universal-generalization rule or either PA194 machine/consistency implication.
Run `check-lift-rename.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set.

An independent fresh Linux replay passed with the audited overlays, rebuilding
its local prerequisites and finding no `sorryAx` in the reported theorem
axioms.
