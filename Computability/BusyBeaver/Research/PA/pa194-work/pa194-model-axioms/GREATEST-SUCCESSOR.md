# A greatest member is a raw successor predecessor

The fixed standard source derivation proves `∀b ∀m. domain(b) → (greatest(b,m) → successor(m,b))` from reflexivity, symmetry and membership congruence. Its closure is kernel-checked, and its three source premises are discharged by previously checked proofs in the classifier-defined full adjunctive separation theory. The resulting closed formula has an actual internal proof in every covered candidate PRA model with IΣ₁ arithmetic reduct.

For arbitrary model-valued b and m, `greatestSuccessorAlignedProof` takes a contextual proof of that universal theorem plus proofs of domain(b) and greatest(b,m), and constructs the exact successor(m,b) instance required by the existing ordinal-step template. A fixed parameter-free Σ₁ graph computes exactly the resulting internal proof code, including for nonstandard indices, contexts and proofs. `greatestSuccessorAlignedFromTheory` supplies the fixed universal theorem by model-level Lean choice, leaving domain and greatest proofs as hypotheses; no uniform graph is claimed for this selection. The existential witness branch, full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-greatest-successor.sh "$PWD" /dev/shm/pa194-greatest-successor-repo
```

The checker rebuilds all three sources in one output against prebuilt dependencies, verifies direct hashes, checks 15 axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
