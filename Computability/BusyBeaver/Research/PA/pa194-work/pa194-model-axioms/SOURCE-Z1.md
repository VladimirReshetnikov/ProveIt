# Full-source zero-domain existence fact

`PA194ZeroDomainExistence.z1` proves the exact `SourceFacts.z1` field in every candidate PRA model whose arithmetic reduct satisfies classical IΣ₁. Its fixed Foundation natural-deduction proof opens the source empty-set axiom, uses the existing `zeroDomain` derivation, and chooses that empty representative as a witness to both domain and zero. The exact quotation of this sentence is identified with `tHyp sZ1`, and the actual source proof code discharges the empty axiom. No other `SourceFacts` field is assumed.

From the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-z1.sh "$PWD" /dev/shm/pa194-source-z1-repo
```

The checker rebuilds the three source modules, requires five clean axiom reports, and rejects `sorryAx`. It retains the updated repository-built naming-facts baseline and other object overlays enumerated in the checker, including prebuilt Foundation. This is a model-uniform Lean theorem, not a native iPRA derivation or the complete source-facts instance.
