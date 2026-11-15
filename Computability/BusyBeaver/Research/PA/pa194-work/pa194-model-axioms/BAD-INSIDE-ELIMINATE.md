# No counterexample inside a domain, in the full source

For every PRA model with IΣ₁ arithmetic reduct, arbitrary internally valid property, and arbitrary model-valued source and point indices, given contextual derivations that the source is a domain, the point belongs to it, the property fails at that point, and the ordinal base and step hold, construct a derivation of any requested formula in the full source. The proof obtains and opens a separation trace for the negated property, inserts the counterexample in that trace, invokes least-bad elimination, and eliminates the trace witness. The full source supplies separation and fixed universal theorems by model-level choice.

This is a model-level construction without an overall fixed Σ₁ proof-code graph yet. The five contextual derivations remain explicit premises. It does not itself establish a successor domain containing an arbitrary domain point, the full ordinal-induction supplier, or a native iPRA machine equivalence. The checker recompiles this source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-bad-inside-eliminate.sh "$PWD" /dev/shm/pa194-bad-inside-eliminate-repo
```

Choose a fresh output for another run.

The source has since been strengthened with a uniform proof-code graph. The checker above now runs the [stronger audit](BAD-INSIDE-ELIMINATE-UNIFORM.md).
