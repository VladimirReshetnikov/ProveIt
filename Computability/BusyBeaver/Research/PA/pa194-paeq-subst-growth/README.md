# PAeq formula substitution output growth

This package adapts the existing arithmetic formula-substitution growth
proof to the current PAeq target language. In every IΣ₁ arithmetic model,
`subst_le_uniform` proves for every internally valid PAeq formula code `p`
and every substitution vector code `w`:

```
subst PA194PAeq.language w p ≤ iter (p+1) (w+3*p+1).
```

The formula and vector may be nonstandard. The proof combines the previously
checked PAeq term/vector and qVec growth bounds, an atomic output bound, and
one-node bounds for all recursive formula constructors. It uses internal Π₁
order induction, available in IΣ₁ models.

This is a bound on the actual output value. It does not provide a bound for
existential witnesses inside the PAeq substitution graph, prove the
arithmetic-to-PAeq translation commutes with substitution, translate proof
codes, or establish a machine reduction. The upstream hashes identify the
adapted input modules.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-subst-growth/check.sh
```

The target atomic, graph-step, and uniform-growth modules passed ordered Lean
suffix checks against the checked target term/qVec modules and retained
arithmetic/project/Foundation prerequisites; their printed axioms contain no
`sorryAx`. The full prerequisite-prefix replay remains pending. The atomic
check is substantially more resource intensive than the other two modules.
