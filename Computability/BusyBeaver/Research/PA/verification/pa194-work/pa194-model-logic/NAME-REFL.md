# Logical naming reflexivity

`PA194GuardedCompiler.nRefl` proves the exact `NameFacts.nRefl` field for any Δ₁ source theory and every internally valid PAeq term, including nonstandard coded terms. It relies solely on the guarded sequent rules and translation's logical constructor/substitution laws: the matrix is an instance of excluded middle. It assumes no source axioms, term-totality facts, fixed arithmetic suppliers, or induction suppliers.

The source also proves a generic guarded excluded-middle theorem and the PAeq free-opening law for `¬p ∨ p`. Replay from the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-nrefl.sh "$PWD" /dev/shm/pa194-nrefl-repo-NEW-new
```

The checker rebuilds the source module against the repository-built `/dev/shm/pa194-name-unique-repo` and retained dependencies listed in the script; it requires three clean axiom reports and rejects `sorryAx`. This is a model-uniform Lean theorem over IΣ₁ arithmetic structures, not a native iPRA object-theory derivation. It establishes one naming field, not the entire interpretation or machine equivalence.
