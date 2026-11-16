# Ordinal-domain membership at arbitrary internal indices

For arbitrary model-valued free indices `a` and `b`, the constructor `memberDomainAtProof` consumes contextual proofs of the fixed universal member-domain theorem, domain(a), and b ∈ a, and constructs a contextual proof of domain(b). It uses the exact `domainOne` and `domainZero` template substitutions at `[b, a]`. Its fixed parameter-free Σ₁ graph is proved to compute exactly the actual output derivation code, including for nonstandard indices, contexts and proof codes.

`memberDomainAtFromLogic` supplies the fixed universal theorem using the previously checked pure-logic internal proof, so its only input derivations are domain(a) and b ∈ a. That universal proof is selected from model-level provability via Lean choice, and no uniform graph is claimed for the selection. These are model-level theorems for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. The complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-member-domain-at.sh "$PWD" /dev/shm/pa194-member-domain-at-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
