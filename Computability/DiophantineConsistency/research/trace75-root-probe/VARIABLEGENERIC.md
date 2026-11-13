# Arithmetic-only variable Pell growth

`PellVariableGrowth.lean` reproduces the previously checked generic
variable-base Pell comparison with one source change: its first import is
`DiophantineConsistency.ArithmeticPellPowerRecovery` instead of
`Direct80ProjectionPell`. All theorem bodies are unchanged. The result
is an arithmetic comparison under explicit coefficient and positivity
hypotheses, with no trace75 graph, halt or iPRA conclusion.

`run-variablegeneric.py`, `observations/variablegeneric-attempt01/`: Lean
exit 0, no warning/error; object
`/tmp/pell-variable-generic-7r3_ts9x/PellVariableGrowth.olean`, SHA-256
`4f082f68b44ec02452f69a012f104ce82debbc46806f9fd83e2d5ad70fdf59f8`.
The replacement arithmetic direct imports are pinned. This source-level
import change does not prove absence of every historical transitive
dependency, nor does it establish full package/source ancestry.
