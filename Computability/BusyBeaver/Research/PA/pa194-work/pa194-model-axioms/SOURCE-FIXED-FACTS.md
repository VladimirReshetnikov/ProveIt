# Full-source fixed facts e1 and s1

`PA194SourceFixedFacts.e1` and `.s1` prove the exact `SourceFacts.e1` and `.s1` fields, respectively, in every candidate PRA model whose arithmetic reduct satisfies classical IΣ₁. They assume no other `SourceFacts` field. The first identifies `tHyp sE1` with the already supplied source equality-reflexivity sentence; the second identifies `tHyp sS1` with the already supplied ordinal domain-successor existence sentence. Both proofs use actual internal source proof objects.

From the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-fixed-facts.sh "$PWD" /dev/shm/pa194-source-fixed-facts-repo
```

The checker rebuilds the quote identities and both field proofs against the updated repository-built naming-facts objects, requires four clean axiom reports, and rejects `sorryAx`. It retains prebuilt dependencies listed in the checker, including Foundation; it does not rebuild their full transitive closure. These are model-uniform Lean theorems, not object-level native iPRA proofs or the full source-facts instance.
