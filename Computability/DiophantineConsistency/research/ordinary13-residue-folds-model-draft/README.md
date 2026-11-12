# Two exact residue-fold model source drafts

This packet proposes **two separate**, all-commutative-ring expression
identities and conditional model/iPRA bridge clients:

- The 88/56 zeta/rank fold is pointwise equal to the 89/56 graph.
- The 87/60 zeta/rank fold is pointwise equal to the distinct 88/60 graph.

They are different parent chains; this packet does not identify the 89/56
parent with the 88/60 parent. All source declarations, simplification/ring
tactics, axiom prints and imported providers are **unelaborated**.

For each pair the source proposes four residual evaluation identities in an
arbitrary commutative ring, combines their squared sums, derives model
same-no-zero, and gives a bridge/native client under an explicit
`PolynomialBridge` hypothesis for that pair's parent. The finite graph
checkers establish exact free-ring fold identities externally, but do not
validate the Lean source or supply either parent bridge. Gamma forcing,
positive-root or root-switch zero maps, compact port representation,
fixed-kernel/PDF binding, parent calibration and provider ancestry retain
their separate unresolved proof obligations.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-folds-model-draft/check.py | cmp - research/ordinary13-residue-folds-model-draft/receipt.json
```

The read-only check reconstructs all four literals, checks their residual
arities and sum DAGs, reruns the authors' exact fold checkers and compares
bounded signed tuple evaluations. It never runs Lean or stages artifacts.
