# Eliminate a bad domain point in the full source

In every PRA model with IΣ₁ arithmetic reduct, for any internally valid property and model-valued domain point, given contextual derivations of the point's domain condition, the negated property, and ordinal base and step, the full-source construction derives any requested formula. It constructs a successor in the domain, opens that witness, derives predecessor membership, invokes the checked bad-point-inside-domain contradiction, and eliminates the successor witness. The fixed universal source theorems and separation inside the nested proof use model-level choice.

This is a model-level construction without its own fixed Σ₁ proof-code graph yet. The four contextual derivations remain explicit premises. Universal closure and packaging as an internal ordinal-induction proof, and the native iPRA machine equivalence, are not established here. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-bad-ordinal-eliminate.sh "$PWD" /dev/shm/pa194-bad-ordinal-eliminate-repo
```

Choose a fresh output for another run.

The source has since been strengthened with a uniform proof-code graph. The checker above now runs the [stronger audit](BAD-ORDINAL-ELIMINATE-UNIFORM.md).
