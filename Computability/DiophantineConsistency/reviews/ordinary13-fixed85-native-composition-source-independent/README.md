# Independent review: fixed-85 native composition

At the source-statement level, the final call supplies the three cut types expected by `fixed_native85` at the identical `fixedK=paramKernel rho`: `crossRootCut` for 81↔83, `gammaCut_of_calibration` applied to the 83 calibration, and the proposed closed 84 `DivCut`. The 87 bridge passed by the intermediate source comes from the fixed 88 model bridge at the same K. The latter uses a proposed `rfl` equality between its tuple and `CompactSymbolicModelIff.p`; neither that equality nor either bridge has been elaborated here.

The target is the **eta-natural 85-row prototype**, with zeta still shifted: its graph has `k=(eta+n_zeta)+1`. It is not the subsequently proposed eta/zeta-natural boundary probe. This review independently compares every row, input and port declaration of the selected `EtaNaturalUnitGraph` against the pinned eta-natural prototype. The theorem's written right-hand side is `∼mappedNativeRefutation embedding`; this source-level inspection does not identify it with the exact external Con(ZFC) sentence, a displayed PDF or an authenticated fixed coefficient tuple.

The checker independently hashes all selected local modules, checks the manifest's lexical import edges, and uses Kahn's algorithm to confirm that this selected local lexical graph is acyclic. It also reproduces the author's rescan and receipt. The scanner has 94 unresolved names, including repository-local modules outside its searched source root as well as external packages. It groups 15 selected bare module names with multiple observed identical-byte candidates. None of these facts decides which providers Lean will use: qualified names are searched under one local root, bare names under research only, and compiled object paths, external modules, Lean parser behavior, source escapes and axioms are outside this check. Source absence from the selected graph is not proof of absence from a compiled provider closure.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-fixed85-native-composition-source-independent/check.py | cmp - reviews/ordinary13-fixed85-native-composition-source-independent/receipt.json
```

The composition has no explicit cut parameter in its final written signature, but all transitive proofs and provider assumptions remain unelaborated. No iPRA derivation, physical PDF binding or end-to-end theorem is established by this review.
