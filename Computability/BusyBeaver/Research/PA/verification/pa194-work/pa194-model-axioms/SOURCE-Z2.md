# Full-source isomorphism of zero representatives

`PA194ZeroIsoGuardedSource.z2` proves the exact `SourceFacts.z2` field in every candidate PRA model whose arithmetic reduct satisfies classical IΣ₁. The checked Foundation source derivation constructs an order isomorphism between two zero representatives under the stated domain guards, using the separately proved actual empty-graph isomorphism and source equality principles. It does not identify the representatives or assume extensionality. The source proof discharges the equality assumptions using actual full-source proof objects; no other SourceFacts field is assumed.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-source-z2.sh "$PWD" /dev/shm/pa194-source-z2-repo
```

The checker rebuilds the standard source derivation, exact `tHyp sZ2` quote identity, and full-source field, with five clean axiom reports and no `sorryAx`. It retains the updated repository-built naming baseline, the repository-built empty-isomorphism module, and other objects listed in the script, including prebuilt Foundation. It is a model-uniform Lean theorem, not native iPRA formalization or a complete SourceFacts instance.
