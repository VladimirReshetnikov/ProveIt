# Shift instantiated fixed formulas and proofs

In every PRA model with IΣ₁ arithmetic reduct, shifting an instance of a shift-fixed internal unary, binary or ternary formula increments each model-valued free index; binary membership has the same property. The unary, ternary, and membership cases also have proof transformers between the original and shifted contexts, with exact values given by the existing fixed Σ₁ `contextShiftCode` graph. The formula and indices may be nonstandard, provided the stated fixedness and typing hypotheses hold. These cover the domain, leastness, and membership formulas used in the greatest witness branch when their fixedness is supplied.

The derivations are hypotheses, and this does not itself insert the extra witness assumption or discharge the full induction sequent. The checker recompiles the source using selected byte-checked repository-built modules; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-fixed-instance-shift.sh "$PWD" /dev/shm/pa194-fixed-instance-shift-repo
```

Choose a fresh output for another run.
