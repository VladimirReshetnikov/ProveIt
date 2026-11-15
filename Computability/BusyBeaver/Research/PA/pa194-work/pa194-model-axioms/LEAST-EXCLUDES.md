# Universal least-point exclusion theorem

The standard source derivation proves that if b is in the ordinal domain, b is least in c, and m ∈ b, then m ∉ c. Its only nonlogical assumptions are the source reflexivity, symmetry and membership-congruence formulas. The template module builds that derivation and kernel-checks its closure as `∀c ∀b ∀m. domain(b) → (least(c,b) → (m ∈ b → m ∉ c))`, without a native-decision axiom.

The model module quotes the derivation, discharges the three assumptions with the previously checked source proofs in the classifier-defined full adjunctive separation theory, and closes the three free variables using internal closure. `leastExcludesUniversalProof` supplies an actual internal proof of the closed formula in every covered candidate PRA model with IΣ₁ arithmetic reduct. Proof selection uses Lean choice. The model-valued specialization, full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-least-excludes-closed.sh "$PWD" /dev/shm/pa194-least-excludes-closed-replay-v3
```

The checker rebuilds both sources in one output against prebuilt dependencies, verifies direct hashes, checks eight axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
