# Conditional QM36→QM37 model transfer

This source-only packet proposes a model and no-zero transfer from the
[36-variable, 155-operation quartic](../adaptive-square-sums36-combined-shift-quartic/README.md)
to its 37-variable parent. It also generates the separate 36-variable,
153-operation factored literal. No Lean or axiom report has run. These are
current-2011-port quartics, not the separate natural-79 compact-port equation.

The literal and 27-residual sources for both 155 and 153 operations are
mechanically transcribed from the pinned candidate graphs. Their ordered
sums of squared residuals are checked externally as exact DAGs; the source
`sum_eq_literal` proofs remain unelaborated.

The 37→36 projection combines the positive parent product inputs at slots 20
and 33. The reverse extension restores them as

```text
productVariable      = productVariable2 * (1 + J*beta)
gammaProductVariable = mainScaleVariable * gamma.
```

The exact model premise is
`((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι beta` for a
**model-natural** `beta : V`. No strict positivity of beta is assumed. The
canonical model order gives `0 ≤ beta`, so `1+J*beta > 0` and both restored
coordinates are positive when the child coordinates are positive. The draft's
fixed-port cast lemma follows the existing current-port source pattern; it too
is unelaborated.

The source defines graph zero-preservation obligations with this cast equality
explicitly quantified in every IΣ₁ model. Its shifted no-zero and native and
standard iPRA clients require those obligations and the earlier QM37 and QM38
obligations. The separate [residual-map draft](../adaptive-qm36-residual-maps-draft/README.md)
proposes proofs of the new graph obligations. No endpoint is unconditional.
The independent [factorized bridge draft](../adaptive-qm36-factorized-ring-bridge-draft/README.md)
proposes the all-port exact 153↔155 ring identity and inherits the same model
premises for its endpoint.

`check_source.py` checks the pinned source rows, input order, represented-beta
interface, residual vectors and 100 finite modular controls for each graph
step. The authors' separate exact external checkers reproduce their output.
None establishes Lean parsing, model equivalence, proof resources, provider
coherence, axiom closure or physical PDF semantics.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm36-conditional-model-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm36-conditional-model-draft/result.json
```
