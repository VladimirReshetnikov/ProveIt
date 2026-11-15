# Ordinal-domain transitivity at model-valued indices

The four modules build a fixed pure-logic derivation of `∀s ∀b ∀m. domain(s) → (b ∈ s → (m ∈ b → m ∈ s))`, kernel-check its three-variable universal closure, quote it into every covered candidate PRA model with IΣ₁ arithmetic reduct, and specialize it at arbitrary model-valued indices. Typed substitution equalities align the domain and membership templates with the one-variable and free-variable syntax used in the minimum-bad argument.

`domainTransAlignedProof` consumes a proof of the fixed universal theorem plus contextual proofs of domain(s), b ∈ s and m ∈ b, and produces m ∈ s. Its fixed parameter-free Σ₁ graph computes exactly the internal output proof code, including for nonstandard indices, contexts and proofs. `domainTransAlignedFromLogic` supplies the fixed theorem proof model-by-model using Lean choice, leaving the three instance proofs as hypotheses; no uniform graph is claimed for the selection. The full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-domain-transitive.sh "$PWD" /dev/shm/pa194-domain-transitive-repo
```

The checker rebuilds all four sources in one output against prebuilt dependencies, verifies direct hashes, checks 19 axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
