# Guarded universal instantiation

`PA194GuardedCompiler.guarded_tr_all_left` gives the one-sided guarded universal-left rule for an internally valid PAeq formula of arity one. Given a guarded derivation containing the negated translation of its instance at a model-valued free-variable index `j`, it derives the corresponding sequent with the negated translated universal. The proof uses the guarded existential rule, so the necessary domain guard for `j` is retained. It assumes no semantic term properties or source axioms; the model-valued formula and index may be nonstandard.

From the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-guarded-all-left.sh "$PWD" /dev/shm/pa194-guarded-all-left-repo-NEW
```

The module rebuilds against the repository-built `/dev/shm/pa194-name-unique-repo` and other object overlays listed in the checker, including prebuilt Foundation; one clean axiom report is required and `sorryAx` is rejected. It is a Lean model-uniform theorem over IΣ₁ arithmetic structures, not native iPRA formalization, a naming field, or a complete interpretation.
