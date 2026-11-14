# Internal finite-context renaming

`PA194RenameContexts.lean` uses IΣ₁ replacement to construct the internal
image of a finite set of formula codes under the generic free-label renamer.
The image exists uniquely for every model-valued parameter and context and
has a fixed Σ₁ graph, defined uniformly from the supplied map graph. Its
membership condition, insertion identity, and preservation of internally
well-formed formula sets are proved. Context and formula codes may be
nonstandard.

For a well-formed context, the image commutes with Foundation's set shift
under the previously proved label-map compatibility equations, both with and
without an output shift. For a depth-one well-formed body and well-formed
context it also proves the exact mapped universal-premise identity:

```
image(p, insert (free φ) (setShift Γ))
  = insert (free (rename(q, φ))) (setShift (image(q, Γ))).
```

Here `f p 0 = 0` and `f p (x+1) = f q x+1` for every model value `x`. The
final corollary supplies these equations for the expanded map with its
protected prefix increased by one on the left.

Results hold in every nonempty candidate-PRA model with equality and an IΣ₁
arithmetic reduct, assuming the supplied Σ₁ map graph is correct for every
model value; the expanded-map graph is fixed and its all-model correctness is
proved. Lean reports `propext`, `Classical.choice`, and `Quot.sound` for the
printed theorem dependencies, with no `sorryAx`. No semantic truth predicate
is used. This package does not transform derivation codes or prove either
PA194 consistency implication.

Run `check-rename-contexts.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.
