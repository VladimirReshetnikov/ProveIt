# Full-source domain-guarded isomorphism symmetry

`PA194IsoSymmetryGuardedSource.is` proves the exact `SourceFacts.is` field in every candidate PRA model whose arithmetic reduct satisfies classical IΣ₁. The standard source derivation uses the existing explicit inverse-graph isomorphism construction under domain guards. Its equality, empty-set, adjunction, intersection and closed inverse-Separation assumptions are discharged using actual full-source proof objects; it assumes no other `SourceFacts` field.

From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-source-is.sh "$PWD" /dev/shm/pa194-source-is-repo
```

The checker builds the standard derivation, exact `tHyp sIs` quote identity, and full-source model field, requiring five clean axiom reports and rejecting `sorryAx`. It retains the updated repository-built naming baseline, inverse-graph source baselines and other object overlays listed in the script, including prebuilt Foundation. This is a model-uniform Lean theorem, not a native iPRA derivation or the complete source-facts instance.
