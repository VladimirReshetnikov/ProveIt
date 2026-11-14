# Shift-closed free-label renaming family

`PA194ExpandedRename.lean` studies, for model-valued `k,a,d,e,x`, the map

```
g(k,a,d,e,x) = x       if x < k
                 k       if x ≥ k, e ≠ 0, and x = a+k
                 x+d     otherwise.
```

The required initial map is `g(0,a,1,1,·)`, equal to
`PA194LiftRename.rename 0 a`. For `0 < d` the map is injective. Eigenvariable
lifting sends its protected prefix from `k` to `k+1`: the lifted map fixes 0
and maps `x+1` to `g(k,a,d,e,x)+1`. Precomposing by the successor map stays
within this family, possibly followed by a successor on the output: for
`k+1`, reduce `k`; for `k=0,a+1`, reduce `a` and increase `d`; and for
`k=0,a=0`, increase `d` and disable the exceptional branch. These identities
hold for arbitrary model values of the parameters; the positive-offset
hypothesis is needed for injectivity, and the initial offset and both closure
operations preserve positivity. The flag is interpreted as disabled exactly
when zero; there is no Boolean-value assumption.

A fixed Σ₁ graph interprets the map with the four parameters packed into a
single model value. The generic internal formula traversal instantiated with
this graph fixes every code in Foundation's concrete PA axiom class, including
nonstandard induction axioms. Results hold in every nonempty candidate-PRA
model with equality and an IΣ₁ arithmetic reduct; the index identities and
injectivity use only its weaker arithmetic consequences. Printed dependencies
are `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.

These are identities of free-variable indices and internal syntax codes, not
yet rule-by-rule compatibility for renaming formula contexts, a finite
candidate-PRA formula-renaming code, or a derivation transformer. No iPRA
consistency implication has been proved here.

Run `check-expanded-rename.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set. It rebuilds dependencies in a fresh temporary
overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local dependencies and finding no `sorryAx` in the displayed theorem
axioms.
