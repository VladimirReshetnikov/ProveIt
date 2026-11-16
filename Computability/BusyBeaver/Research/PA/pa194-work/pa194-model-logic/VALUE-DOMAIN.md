# Every term-value formula includes its domain condition

`PA194GuardedCompiler.valBody_has_domain` proves that, for every internally valid arity-zero PAeq term `s`, its source value formula is exactly `domainCode #0 ∧ r` for some internally valid arity-one source formula `r`. The term and remainder may be nonstandard model elements. The proof supplies an explicit parameter-free Σ₁ definability instance for `valBody` and uses the existing fixed Σ₁ term-induction theorem with all five constructor equations. This is a syntactic factorization; it assumes no source theory or naming-field premise.

From the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-value-domain.sh "$PWD" /dev/shm/pa194-value-domain-repo-NEW-new
```

The checker recompiles the module against the repository-built `/dev/shm/pa194-value-body-repo` and other retained overlays listed in the script, including prebuilt Foundation; it requires two clean axiom reports and rejects `sorryAx`. The result is model-uniform for IΣ₁ arithmetic structures. It does not itself show term-value existence or uniqueness, prove any remaining semantic naming field, or formalize the iPRA machine equivalence.
