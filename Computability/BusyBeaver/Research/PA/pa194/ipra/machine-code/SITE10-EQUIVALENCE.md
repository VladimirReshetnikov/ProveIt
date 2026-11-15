# Conditional literal-halt / source-site-10 equivalence

`PA194Site10Equivalence.literalHaltIffSite10` is an all-model Lean theorem for every candidate PRA model whose arithmetic reduct satisfies IΣ₁. It states that the literal packed machine reaches control ≥194 at some model time if and only if a specified finite PR run code reaches a state whose specified finite PR program-counter code evaluates to model numeral 10.

Both directions depend on these explicit hypotheses:

* For every model index before the first PC=10 hit, the physical run at the displayed model-valued elapsed clock is synchronized with a packed control-24 frame for the coded state, the state's `good` predicate holds, and that index is at most the elapsed clock. The active flag is the checked finite PR no-prior-hit code.
* Every coded state whose PC equals 10 has the tape representation `pair(left s, modelWord (PA194SourceProgram.path 10) (suffix s))`. Left tape and suffix are arbitrary model values; non-hit states are not constrained to have that path.

The proof composes bounded active-hit extraction, model-uniform physical halt persistence, root-frame nonhalting, the actual kernel-checked site-10 path `[false,false,true]`, and its exact three-step literal halt segment. It does not construct or certify the actual controller run/PC codes, establish either hypothesis, connect scheduler halt to PC=10, or derive an object-iPRA/Con(PA) statement. The designated start frame is a parameter.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site10-equivalence.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker recompiles fourteen sources in a single fresh output, verifies selected hashes, rejects inherited Git overrides, and audits printed axioms. The machine baseline, graph/equality-code overlay, and project and package foundations remain prebuilt. Their full transitive provenance and cross-overlay compatibility have not been independently reconstructed; this is not a self-contained full source build.
