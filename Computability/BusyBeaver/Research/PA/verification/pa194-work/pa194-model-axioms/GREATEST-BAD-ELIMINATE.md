# Eliminate the greatest predecessor witness in the full source

For every PRA model with IΣ₁ arithmetic reduct and arbitrary internally valid property and model-valued indices, this constructs a derivation of an arbitrary formula from supplied contextual derivations of the bad trace, source domain, bad-point membership, bad-point domain, leastness, induction step, and existence of a greatest predecessor. The proof shifts and weakens all relevant derivations into the freshly opened witness context, changes the irrelevant leastness index, derives a contradiction using the opened greatestness assumption, and eliminates the existential witness. Fixed universal source theorems are supplied by model-level choice.

This is a model-level full-source construction, not yet accompanied by a fixed Σ₁ graph for its overall proof code. The listed derivations, including greatest-existence and leastness, remain explicit premises. It does not yet discharge the least witness or ordinal induction, or prove the native iPRA theorem or machine equivalence. The checker recompiles the source using selected byte-checked repository-built modules; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-greatest-bad-eliminate.sh "$PWD" /dev/shm/pa194-greatest-bad-eliminate-repo
```

Choose a fresh output for another run.

The source has since been strengthened with a uniform proof-code graph. The checker above now runs the [stronger audit](GREATEST-BAD-ELIMINATE-UNIFORM.md).
