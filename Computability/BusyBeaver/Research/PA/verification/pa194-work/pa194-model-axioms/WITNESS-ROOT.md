# Direct elimination of the separation witness

This composes the checked specialization of `sepRoot p` at model-valued index `s` with elimination of the resulting existential trace witness. For any covered candidate PRA model with IΣ₁ arithmetic reduct, internal Δ₁ theory, arbitrary internal context, valid arity-one property p, and internal index s, the constructor takes a contextual proof of `sepRoot p` and a proof of the conclusion in the shifted context with the opened witness as an assumption. It produces a contextual proof of the conclusion. The fixed parameter-free Σ₁ graph is proved to compute the exact resulting internal proof code; all input codes can be nonstandard.

Both input proofs remain hypotheses. The branch proof is the substantive missing part of this ordinal-induction step; this result does not establish the ordinal induction sequent or native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-separation-witness-root.sh "$PWD" /dev/shm/pa194-separation-witness-from-root-replay
```

The checker rebuilds the source against prebuilt dependency outputs, verifies direct input hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
