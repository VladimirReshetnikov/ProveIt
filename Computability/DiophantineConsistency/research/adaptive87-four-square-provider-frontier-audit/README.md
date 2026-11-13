# Bounded provider frontier for the 88/30 model draft

This is a **read-only lexical and object-presence inventory**, not a build plan authenticated for execution. It selects the three unelaborated sources in `research/adaptive87-four-square-current88-model-draft/`, including the added explicit `ModelArithmetic` import. It does not run Lean, copy providers, modify earlier evidence, authenticate objects, or prove an endpoint.

The selected direct import graph is:

* `AdaptiveFourSquare88Graph` → `AdaptiveFirstRootFactor87Literal`;
* `FourUnitGeneric` → `ModelCarrierScaled`, `ArithmeticAdaptiveFactorUnits2011`;
* `FourSquare88Model` → the two selected modules, `HAExpressionSameZero`, `IPRAExpressionNative`, and `ModelArithmetic`.

All names in the last list, apart from the two draft modules, are qualified by `DiophantineConsistency`. `ModelArithmetic` imports `ModelDifferenceRing`. The model client's 87 `PolynomialBridge` remains an explicit premise: instantiating it would add a separate source and provider obligation. The historical HA87 theorem and translated-refutation iPRA endpoint do not on their own authenticate the draft's mapped-native iPRA client.

The retained run reads the actual initial import prefixes, hashes the three draft files and each reachable current `Lean/DiophantineConsistency` source, and records 683 project sources, no missing project sources **under that one root**, and 124 distinct external frontier names. These include `Mathlib`, `Foundation`, `ZFCinPA`, `BusyBeaver`, `Diophantine`, `PAHF`, and `Lean`; their transitive source or object closure was not scanned. The 683 count excludes the three selected draft files. The import parser is deliberately lexical, limited to initial ordinary or public `import` lines, and cannot rule out dynamically introduced dependencies or source-configuration differences.

The candidate object observations in `result.json` are a point-in-time check for exactly those 683 source names:

| Candidate root | Present | Absent |
| --- | ---: | ---: |
| `/tmp/ha87-full-transitive-p3xt6wra/lib` | 292 | 391 |
| `/tmp/current14-standard-fresh-build-20261104/lib` | 561 | 122 |
| `/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib` | 0 | 683 |

In the first two roots 210 names overlap and 40 are absent from both. The complete named lists and direct-object hashes are in the receipt. In particular, the HA87 root has the parent 87 literal and factor units, but neither root has `ModelCarrierScaled`, `HAExpressionSameZero`, `IPRAExpressionNative`, or `ModelArithmetic`. The package root was inspected only for these *project-qualified names*; its zero count says nothing about its intended external package contents. A present object is not proof of a compatible object: the current source matches 561 available current14 snapshot sources, while 35 of the 292 available HA87 object's corresponding historical source files differ from the current source. The receipt lists those names. A specific interface mismatch is visible: in the historical HA87 snapshot `ArithmeticAdaptiveFactorUnits2011.first_bad`, `main_bad`, `strong_bad`, and `aux_bad` were private; current source makes them public, and the new `FourUnitGeneric` source mentions all four. The historical object therefore cannot be presumed to expose the public declarations that this draft calls; an authenticated current-source provider or a different client interface is required. The checker pins both source hashes and verifies the private/public markers. This source comparison is not an authentication of the objects or their imported providers, and the two candidate roots must not be treated as a validated combined environment.

The historical HA87 full-source author-pass evidence and its limitations are described in `reviews/ha87-isolated-full-author-pass/README.md`. The present scanner neither replays nor reauthenticates it. Toolchain and package objects, companion files, search-path collision precedence, imported-object consistency, actual source compilation, and the final theorem/axiom reports remain open. Free space, running processes, and safeguards must be independently checked at any future build; this scan makes no readiness claim.

Reproduce from the DiophantineConsistency directory, with the named historical `/tmp` roots still available:

```sh
python3 research/adaptive87-four-square-provider-frontier-audit/check.py > /tmp/adaptive87-frontier-current.json
cmp research/adaptive87-four-square-provider-frontier-audit/result.json /tmp/adaptive87-frontier-current.json
```

A differing result may reflect changed current sources or ephemeral provider state and requires investigation; the script opens no Lean process and reads rather than changes those provider roots. The only output above is a new scratch receipt.
