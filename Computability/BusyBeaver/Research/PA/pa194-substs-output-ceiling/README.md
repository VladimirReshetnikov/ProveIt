# Uniform arithmetic substitution output and witness bound

`substitution_output_le` derives a common arithmetic substitution-output
ceiling from the existing `PA196PASubstitutionUniformGrowth.subst_le_uniform`
theorem and monotonicity of the tower iterator. In every candidate-PRA model
whose arithmetic reduct satisfies IΣ₁, if a valid arithmetic formula code `p`
and substitution vector code `w` are both at most `c`, then

```
subst ℒₒᵣ w p ≤ iter (c + 1) (c + 3*c + 1).
```

`common_substitution_witness_ceiling` combines this bound with the preceding
uniform witness result. For any `c` there is a single model element bounding
all existential witnesses in the arithmetic substitution graph for the
actual substitution results of every such `p` and `w`. The formula, vector,
ceiling, and witness bound may all be nonstandard model elements.

The witness bound is selected using the model-level `WB` theorem; no finite
PRA code or definable selection for it is constructed. The target PAeq
substitution graph and arithmetic-to-PAeq translation graph still need their
own bounds, and the full fixed-parameter substitution-agreement invariant
has not been proved.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-substs-output-ceiling/check.sh
```

The final module passed a fresh suffix check against retained qVec,
substitution-witness, and output-growth prerequisites and the audited project
and Foundation overlays. Its printed axioms contain no `sorryAx`. The full
prerequisite-prefix replay remains pending.
