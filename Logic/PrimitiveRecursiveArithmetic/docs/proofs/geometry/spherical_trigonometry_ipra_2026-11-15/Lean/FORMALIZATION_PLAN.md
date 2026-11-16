# Lean completion plan

## Status

The three Lean files are uncompiled prototypes because the delivery container
has no `lean` or `lake` executable. `SphericalKernel.lean` contains no `sorry`
or custom axioms and is intended to be the first compiling target.
`SphericalTrig.lean` proves representative algebraic consequences and records
the presentation interfaces. `IPRABridge.lean` defines the actual
ConciseIPRA-facing data and makes the endpoint an explicit structure whose
`derivation` field must be a closed `Prf PRAAx` term.

An ambient Mathlib theorem is not an object-language iPRA theorem. The final
acceptance criterion is construction of `InternalAtlasTarget` and
`InternalTetrahedronTarget` values.

## Dependency order

1. Compile `SphericalKernel.lean`; repair any Mathlib 4.32 syntax differences.
2. Audit its final declarations with `#print axioms`.
3. Compile `SphericalTrig.lean` and import the existing constructive
   `TrigSystem` rather than duplicating it once module paths are stabilized.
4. Implement signed-rational and dyadic codecs as concrete `PR` symbols.
5. Implement dot, cross, determinant, bounded square root, exponential, and
   arctangent constructors on rapid names.
6. Prove fixed-precision closure estimates using `PRA.qfInd` only on
   quantifier-free loop invariants.
7. Implement a sparse-polynomial certificate checker and prove evaluator
   soundness inside `PRAAx`.
8. Realize the spherical core from three unit-vector names and build angle names
   using one retained two-chart `atan2` decision.
9. Prove cross-multiplied formula families, then guarded quotient/root forms.
10. Implement the equal-area chart and boundary-strip modulus for finite
    geodesic polygons; derive Girard and polygonal excess.
11. Formalize tetrahedral face vectors and import the planar sine law for the
    sine-product theorem.
12. Assemble the closed formulas, construct the `Prf PRAAx` terms, and only
    then invoke `pra_theorem_iff` or `pra_iff_native`.

## Expected validation

```bash
lake env lean Lean/SphericalKernel.lean
lake env lean Lean/SphericalTrig.lean
lake build ConciseIPRA.NativeBiInterpretation
lake env lean Lean/IPRABridge.lean
```

Then run the exact Python checker and compare its ledger to the theorem names.
No `sorry`, extra arithmetic axioms, `native_decide`, or hidden classical
real-equality tests should occur in the final object-level path.
