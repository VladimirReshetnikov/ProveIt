# Sources and trust boundary

## Requested source

- Wikipedia, **Expected value**, revision `oldid=1385865607`, accessed
  2026-11-16.  The audit follows the article's definitions, examples,
  distribution table, properties, inequalities, convergence section,
  characteristic-function discussion, and applications.

## ProveIt baseline

Repository: `VladimirReshetnikov/ProveIt`.

Inspected main-branch commit:

```text
df3ff8cc28be5eb713a14809a9df167e9aa94ab1
```

Relevant files and directories:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/BoundedSums.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/SumLemmas.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/MultiSums.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/central_limit_ipra_2026-11-15/`
- in particular its `lean/FiniteCLTBlueprint.lean` and
  `lean/ObjectLanguageTarget.lean` regular-name and object-language patterns.

## Trust boundary

1. The mathematical arguments in the PDF are human-readable proofs.
2. `validation/validation.json` records exact finite computations, but those
   computations are not part of a formal theorem proof.
3. The supplied Lean files are design scaffolds and were not compiled in the
   preparation environment, which did not contain Lean/Lake.
4. Existing ProveIt derivations cited as reusable are kernel-checked in their
   repository; this packet does not claim that its new probability theorems
   have already been added to that checked library.
5. Analytic extensions require the explicit moduli stated in the manuscript.
   No appeal is made to an unrepresented arbitrary real, measure, Borel set, or
   choice principle.
