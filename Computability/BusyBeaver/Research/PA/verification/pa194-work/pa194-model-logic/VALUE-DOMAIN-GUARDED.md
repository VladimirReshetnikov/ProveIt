# Guarded term-value domain projection

`PA194GuardedCompiler.guarded_valBody_domain` proves, for every internally valid arity-zero term `s`, model-valued free-variable index `j`, and Δ₁ source theory, the guarded sequent `¬valBody(s)[&j] ∨ domain(&j)`. The term and index may be nonstandard. The proof opens the independently checked `valBody_has_domain` factorization, distributes substitution, and applies source propositional rules; no source axioms or naming-field assumptions are needed.

From the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-value-domain-guarded.sh "$PWD" /dev/shm/pa194-value-domain-guarded-repo-NEW-new
```

The checker rebuilds the module against the independently source-replayed `/dev/shm/pa194-value-domain-replay`, the repository-built value-body baseline, and retained objects listed in the script, including prebuilt Foundation. It requires one clean axiom report and rejects `sorryAx`. This model-uniform IΣ₁ result does not establish term-value existence, `eSucc`, a complete interpretation, or an object-level native iPRA theorem.
