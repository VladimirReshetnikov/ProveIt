# PAeq term substitution growth

This package adapts the existing arithmetic term-substitution growth proofs
to the current PAeq target language, whose function symbols have arity at
most two. In every IΣ₁ arithmetic model, including on nonstandard inputs,
`termSubst_le` bounds the numeric output of target term substitution, and
`termSubstVec_le` bounds substituted term vectors. The proofs also include the
numeric bound `relation_le` for a relation code containing such a vector.

These are output-size bounds. They do not prove the full formula-substitution
bound, a witness bound for the target substitution graph, or translation
compatibility. The upstream hashes identify the adapted input files.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-term-subst-growth/check.sh
```

The final modules passed ordered suffix checks against the checked target
shift-growth object and retained arithmetic/project/Foundation prerequisites.
Their printed axioms contain no `sorryAx`. The full prerequisite-prefix replay
remains pending.
