# Isolated mod-4 and generic no-zero alternatives for 88/30

These two `.lean.src` files are **unelaborated proposals**, preserving the original model packet. They target the exact 13-variable current-port four-square draft and retain its explicit hypothesis `PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87` in both the bridge and the native endpoint. Neither source proves that hypothesis; no iPRA endpoint is established here.

`FourUnitGeneric.lean.src` is the original generic client with its direct `ArithmeticAdaptiveFactorUnits2011` import and namespace opening removed. Its four residue facts are copied verbatim from that source, with `private` visibility, into its own namespace; their existing finite proofs are `by decide`. It adds explicit `Mathlib.Data.ZMod.Basic`, `Mathlib.Tactic.LinearCombination`, and `Mathlib.Tactic.Linarith` imports. All other executable proof text and the exported theorem signatures are unchanged. The independent Python residue controls enumerate 64, 256, 64 and 256 assignments respectively; they check the displayed modular arithmetic but do not elaborate Lean.

`FourSquare88Model.lean.src` is the original model client with the `HAExpressionSameZero` import replaced by `HAExpressionNoZeroEquiv`, a local pointwise `SameZero` definition of the same form, and the generic `HAExpressionNoZeroEquiv.bridge` applied to the universally quantified negations of that pointwise equivalence. Its unchanged factor proof and parent valuation are retained. This is a proposed source substitution, not a verified ABI or theorem export; the selected logical names must be used consistently in any future isolated build.

The distinction between the conditional client and an instantiated endpoint is essential:

* The current-source lexical closure of **the combined conditional alternatives** contains 458 project sources and has no path to `ArithmeticAdaptiveFactorUnits2011`. This conclusion is only for scanned source-header imports, not for dynamic imports, packages, or compiled objects.
* The original model client imports `HAExpressionSameZero` and reaches FactorUnits through `HAAdaptiveDirectOrdinate86Units`. That 86 client uses the four residue theorems, syntax/evaluation helpers private in the historical HA87 snapshot, and `units_of_residues`, which is absent from that snapshot. Therefore the original client's full source closure still needs the newer interface.
* Instantiating the alternative client with `HAAdaptiveFactor87.polynomialBridge` reintroduces FactorUnits. `result.json` records the full import chain through `ArithmeticAdaptiveEquivalenceUnconditional2011` and `ArithmeticAdaptiveConstructionFactorZero2011`. The source closure of the conditional client plus that instantiation has 658 project sources and 124 external import names. The no-FactorUnits observation must not be applied to this combined endpoint.

A read-only presence scan of the two historical project object roots finds 14 combined-closure project names absent from both; the complete named list and counts are in the receipt. In particular, the newly selected generic `HAExpressionNoZeroEquiv`, `IPRAExpressionNative`, `ModelArithmetic`, and `ModelCarrierScaled` are not supplied by either surveyed root. A file elsewhere might supply them; no exhaustive provider search is claimed. Where an object is present, this check neither authenticates its source provenance nor shows that its direct and transitive objects are compatible. The separate `research/adaptive87-four-square-provider-frontier-audit/` documents historical/current source drift and the other unchecked provider boundaries. No build readiness follows from these observations.

Run the bounded deterministic check from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-four-square-local-mod4-model-draft/check.py > /tmp/adaptive87-local-mod4-current.json
cmp research/adaptive87-four-square-local-mod4-model-draft/result.json /tmp/adaptive87-local-mod4-current.json
```

It pins the two original draft sources, the exact current FactorUnits source, the existing no-zero bridge, the earlier lexical scanner and receipt, both proposed alternatives, and all source bytes in the inherited closure; it independently recomputes the full instantiated source closure. It checks the exact allowed text changes, old/private versus current/public names used by the 86 source, and all stated finite cases. It reads the historical `/tmp` providers, whose existence and contents can change. It does not run Lean, stage files, modify any provider, or authenticate compiled objects.
