# Lean completion plan

## Status

The two `.lean` files in this directory were **not compiled** in the
artifact-building runtime because Lean 4.32.0 was unavailable.  The semantic
file contains explicit `sorry` placeholders for nontrivial proofs.  The object
blueprint imports the repository's actual `ConciseIPRA` modules but uses
schematic `True` targets where the final encoded formulas have not yet been
written.  No completed `Prf PRAAx` theorem is claimed.

## Pinned environment

- Repository: `VladimirReshetnikov/ProveIt`
- Snapshot inspected: `b88e843c31b50dfe461bfbd0380166ca422cd3ab`
- Expected Lean toolchain: `leanprover/lean4:v4.32.0`
- Namespace: `LeanProofs.ConciseIPRA`

## Dependency order

1. **Coding PR terms**
   - numerals and constants of arbitrary arity
   - Boolean normalization, `and`, `or`, equality and order tests
   - `max`
   - 2-adic pair and projections
   - coded length, lookup, append, update
2. **Defining equations**
   - use `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`
   - establish Boolean range lemmas (`b = 0 ∨ b = 1`) as QF formulas
3. **Bounded folds**
   - `allBelow`, `anyBelow`, `firstTrue`
   - object proofs of zero/successor equations and correctness
4. **Trace runner**
   - one concrete `PR.prec` code with stage first
   - state-freezing after the horizon
   - lookup/update lemmas for the encoded trace table
5. **`PRA.traceReflection`**
   - define the exact `Fm PTm` invariant
   - prove `.QF`
   - instantiate `PRA.qfInd`
6. **Reverse demand**
   - generate a fixed reverse-fold term from a meta-level DAG descriptor
   - prove edge adequacy by another QF loop invariant
7. **Node combinators**
   - deterministic map
   - product
   - sequential composition
   - guarded/overlapping branch
   - bounded search
   - finite relational refinement
8. **`PRA.contractDAGReflection`**
   - global invariant is a Boolean fold over processed nodes
   - local `Prf` values are composed in the successor case
9. **Cubic benchmark**
   - rational codes and cross-multiplied order
   - exact midpoint and cubic evaluation
   - bisection trace invariant
   - residual factorization and quantitative uniqueness
10. **Native export**
    - apply `pra_iff_native` only after the object theorem exists

## Suggested validation commands

```sh
lake env lean lean/FiniteContractSemantic.lean
lake env lean lean/ObjectCompilerBlueprint.lean
```

Then replace every `sorry` and every schematic `True` target, run:

```sh
grep -R --line-number -E 'sorry|axiom|admit|True := by' lean
lake build
```

Finally use `#print axioms` on all exported theorems and record the output.

## First realistic pull request

The smallest valuable upstream change is not the whole DAG compiler.  It is:

1. a compiled object-level `allBelow`/`anyBelow` library;
2. a compiled coded trace runner;
3. `PRA.traceReflection`;
4. one nontrivial instantiation, preferably the cubic bisection theorem.

That pull request would turn many packet roadmaps from prose into shared,
kernel-checked infrastructure.
