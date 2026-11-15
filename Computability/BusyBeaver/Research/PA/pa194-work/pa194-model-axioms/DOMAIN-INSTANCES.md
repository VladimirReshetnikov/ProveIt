# Domain instance correspondence and member-domain application

For arbitrary model-valued indices `a` and `b`, the source proves exact equality of the two-variable ordinal templates `domainOne` and `domainZero` specialized at `[b,a]` with the one-variable `domainTemplate` specialized at `a` and `b`, respectively. The proof uses typed substitution composition and covers nonstandard indices.

`memberDomainOneVarProof` uses these equalities to construct domain(b) from contextual proofs of the universal member-domain theorem, domain(a), and b ∈ a in the one-variable syntax used by ordinal induction. Its output code is exactly the already-checked fixed Σ₁ `memberDomainAtCode` graph. `memberDomainOneVarFromLogic` supplies the universal theorem by model-level choice, leaving only the domain and membership proofs as hypotheses; no uniform graph is claimed for the theorem selection. The complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-domain-instances.sh "$PWD" /dev/shm/pa194-domain-instances-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks five axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
