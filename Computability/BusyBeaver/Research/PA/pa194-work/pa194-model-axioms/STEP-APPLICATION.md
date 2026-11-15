# Uniform ordinal step application proof code

The sources give fixed parameter-free Σ₁ arithmetic graphs for double specialization, generic contextual two-variable step application, and the actual ordinal-step application. Each graph is proved to compute exactly the code of the corresponding internally constructed derivation. The results apply in each covered candidate PRA model whose induced ordered ring models IΣ₁, to internal Δ₁ source theories, valid internal formulas, arbitrary internal terms or indices and contexts, including nonstandard inputs.

The ordinal-step constructor consumes actual derivations under the same context of the step statement, both domain instances, successor and the property at the predecessor, and supplies a derivation of the property at the successor. Those five input derivations remain hypotheses. This result does not derive the ordinal induction sequent, identify PA with the source theory, or establish a native iPRA theorem.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-step-code.sh "$PWD" /dev/shm/pa194-ordinal-step-application-code-replay
```

The checker source-replays all three modules into one output directory, checks SHA-256 hashes for them and three direct prebuilt dependency objects, and lists the remaining prebuilt dependency directories. Its nine axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.
