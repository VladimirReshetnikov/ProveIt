# Proposed 37↔38 graph zero maps from residual identities

This is an inert Lean source draft intended to discharge the explicit
`GraphZeroObligations` in the separate
[conditional 37-variable transfer](../adaptive-qm37-conditional-model-draft/README.md).
It has not been parsed or elaborated by Lean; all source tactics and axiom
reports remain untested.

The draft proposes 26 direct difference-ring residual comparisons, two
parent-square residuals that vanish on extension, and the special identity

```text
parentAux = childAux + Q * childDifference.
```

The child's difference residual is zero at any child zero. For projection of a
parent zero, the separately proposed positive-difference witness makes that
residual zero; the two parent square residuals permit extension after
projection to recover the original parent valuation. The source then proposes
to assemble all 29 parent or all 28 child residual zeros, yielding the two
zero maps and `graphZeroObligations` without adding mathematical assumptions.
The previous draft's positive-difference proof, sum-of-squares lemmas and
38↔40 model obligations remain dependencies; none is Lean-checked here.

The read-only checker verifies all 26 retained residual index mappings, the
two removed parent indices 4 and 21, child difference index 4, the stated aux
coefficient slot, and the earlier external exact residual receipt. It does
not verify the Lean tactic scripts, prove a model theorem, authenticate
providers, or bind a physical page. The separate candidate's exact integer
polynomial checker reproduces its output and provides external supporting
algebra.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm37-residual-maps-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm37-residual-maps-draft/source-result.json
```

`generate.py` regenerates only the inert proof source in this packet; no Lean
or staging is performed.
