# Conditional four-case guarded interpretation

`PA194GuardedInterpretationReductionFour.lean` assembles the guarded `Interpretation` using the four-case axiom reduction, source inhabitation and the Leibniz witness construction. It assumes `TermFacts` for the full source theory, typed suppliers for addition congruence, multiplication congruence, addition-successor and multiplication-successor, and a translated closed-induction supplier for every internally valid arity-one PAeq property, including nonstandard codes. `refutation_of_remaining` transports an internal ordinary PAeq proof of falsity to source-theory provability of falsity under the same hypotheses.

From the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-interpretation-reduction-four.sh "$PWD" /dev/shm/pa194-interpretation-reduction-four-replay-new
```

The checker recompiles the wrapper and its two axiom reports and rejects `sorryAx`. It uses the independently source-replayed `/dev/shm/pa194-interpretation-axioms-four-replay` and retained fixed-four/successor overlays, plus repository-built inhabitedness, Leibniz and other overlays enumerated in the checker; Foundation and package objects are prebuilt. This is a model-uniform Lean theorem for candidate PRA + classical IΣ₁, not a theorem formalized in native iPRA. The assumed suppliers and physical scheduler synchronization remain unproved by this module.
