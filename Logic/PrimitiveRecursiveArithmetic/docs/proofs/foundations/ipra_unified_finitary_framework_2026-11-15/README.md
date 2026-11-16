# Unified finitary-relational framework for mathematics in iPRA

This archive develops a reusable framework for translating mathematical
objects, algorithms, certificates, and approximate witnesses into
intuitionistic primitive recursive arithmetic (iPRA).  It was prepared against
ProveIt commit `b88e843c31b50dfe461bfbd0380166ca422cd3ab`.

## Main deliverables

- `paper/ipra_unified_framework.pdf` - 58-page research report.
- `paper/ipra_unified_framework.tex` and `paper/sections/*.tex` - complete
  LaTeX source.
- `lean/TraceCompilerBlueprint.lean` - source-oriented blueprint for a generic
  compiler whose inputs and output are actual `Prf PRAAx` derivations.
- `lean/RelationalRefinementBlueprint.lean` - viability and
  shrinking-refinement definitions/theorem targets.
- `lean/ApplicationTargets.lean` - guarded regular-name, finite-net, and
  height/list targets.
- `code/reference_framework.py` - exact finite reference implementation using
  standard-library Python and `Fraction` arithmetic.
- `code/test_reference_framework.py` - eight regression tests.
- `THEOREM_LEDGER.md` and `metadata/` - claim status, difficulty matrix,
  machine-readable framework schema, and source provenance.

## Principal synthesis

1. **Proof-producing finite traces.**  A bounded computation is described by
   fixed primitive-recursive `good`, `init`, `bound`, `step`, `inv`, and
   `accept` symbols.  Given embedded base, step, and final derivations, a
   generic construction produces the completed `Prf PRAAx` derivation using
   quantifier-free induction and the primitive-recursion equations.
2. **Finitary relational presentations.**  Non-unique approximate outputs are
   finite verified answer clouds with compatibility edges, not forced exact
   selectors.
3. **Finite witness amalgamation.**  Backward viability removes dead ends and
   constructs compatible finite paths by bounded search.
4. **Shrinking viability.**  The least candidate lying on a complete path to a
   changing finite horizon gives a coherent primitive-recursive name when
   full-viable clouds have an explicit diameter modulus and compatible edges
   have a summable motion budget.  No infinite branch is selected.
5. **Honest producer boundaries.**  Height bounds, analytic constants,
   rational covering representatives, singular branches, and other deep data
   are separated from their uniform finite verifiers.

## Exact status

The report supplies complete human arguments for the generic Booleanization,
trace-reflection, composition, finite-amalgamation, shrinking-viability,
guarded-extensionality, finite-net, and height/list theorems.  The Python
reference checks pass.

The Lean files are **blueprints, not completed formalizations**.  Lean/Lake was
not available in the artifact environment.  The key object-language formulas
and derivations contain visible `sorry` placeholders or target declarations;
no claim is made that the generic `Prf PRAAx` compiler or applications have
been kernel-checked.

## Reproduce

From the archive root:

```sh
bash build.sh
```

This runs the exact Python tests and compiles the PDF with `latexmk`.  The
checked results from this build are in `validation/`.
