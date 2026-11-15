# Apply successor-membership at model indices

In every PRA model with IΣ₁ arithmetic reduct and any internal theory, specialize the fixed universal successor-membership theorem at arbitrary model-valued predecessor and successor indices. Given contextual derivations of that universal theorem and the successor relation, construct a derivation that the predecessor belongs to the successor. The exact proof code has a fixed Σ₁ graph and the successor/membership templates are aligned with those used in the induction proof.

Both derivations are explicit premises. This does not itself open a successor witness, complete ordinal induction, or establish iPRA machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-successor-member-at.sh "$PWD" /dev/shm/pa194-successor-member-at-repo
```

Choose a fresh output for another run.
