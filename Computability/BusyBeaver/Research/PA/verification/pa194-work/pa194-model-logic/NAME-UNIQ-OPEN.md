# Open guarded uniqueness consequence

`nameOfUniq_open` proves, for any internally valid PAeq arity-zero term `t` and model-valued free-variable indices `j,k`, the guarded sequent `¬tr(uniq t), ¬tr(k=t), tr(¬(j=t) ∨ j=k)` in any Δ₁ source theory. The term and indices may be nonstandard. It instantiates the uniqueness formula twice using the guarded universal-left rule and the separately checked substitutions, then applies a purely propositional guarded sequent. No source axioms or semantic properties of terms are assumed.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-name-uniq-open.sh "$PWD" /dev/shm/pa194-name-uniq-open-repo-NEW-new
```

The two source modules are rebuilt and checked for `sorryAx`, with one clean axiom report each; the checker retains the separately replayed uniqueness-substitution overlay and the repository-built guarded universal-left module, plus prebuilt dependencies including Foundation. The quantified `NameFacts.nameOfUniq` field, native iPRA theorem and full interpretation are separate obligations.
