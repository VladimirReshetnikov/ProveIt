# Conditional full-source multiplication coherence

This chain constructs the pointwise and universally quantified multiplication-coherence successor cases, the actual source ordinal-induction step and conclusion, the exact closed negated-coherence Separation instance, and a model-level source-theory discharge. `PA194MulCoherence.sourceProof` returns an internal full-source proof of the global multiplication-coherence statement from one explicit premise: an internal proof of the stronger addition-coherence statement. It handles arbitrary candidate PRA models carrying classical IΣ₁ and uses actual predecessor/isomorphism witnesses. The source proof pays strict and inclusive Separation and the negated-coherence Separation axiom.

The stronger addition-coherence premise remains explicit, as does the separate addition-order bridge for `sM3`; no full `sM3`, native iPRA theorem or machine synchronization is claimed.

From the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-mul-coherence-conditional.sh "$PWD" /dev/shm/pa194-mul-coherence-conditional-repo
```

The incremental checker rebuilds 13 local source modules in one output, rejects `sorryAx` and checks 21 axiom reports. It prioritizes `/dev/shm/pa194-add-coherence-apply-closure-repo`, repository multiplication coherence/m1/graph and Separation objects, the repository-built multiplication-predecessor chain and repository-built inside/properties/rules objects. Addition coherence application itself was repository-replayed against an older staged lower closure with documented path-order/segmentation-fault concerns; full lower source-closure provenance remains unverified. Earlier addition and Foundation objects are also retained.
