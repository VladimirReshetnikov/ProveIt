# Universal ordinal member-domain theorem

The fixed ordinary source derivation proves `∀a ∀b. domain(a) → (b ∈ a → domain(b))` from pure logic, using the existing `memberDomain` construction. The template module constructs the standard open proof and its kernel-checked universal-closure identity; no native-decision axiom is used. The model module quotes the standard derivation, closes its two free variables via the existing internal closure theorem, and constructs an actual internal proof of the resulting universally quantified formula in every covered candidate PRA model with IΣ₁ arithmetic reduct and every internal Δ₁ source theory. It has no source-axiom or formula-specific proof premises.

The internal proof is selected from model-level provability using Lean choice; this module does not provide a uniform graph for the selection or yet specialize the theorem at arbitrary model-valued indices. The full ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-member-domain-closed.sh "$PWD" /dev/shm/pa194-member-domain-closed-replay-v2
```

The checker rebuilds both sources in one output against prebuilt dependencies, verifies direct hashes, checks nine axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
