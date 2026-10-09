# Integration contract

## Inspected baseline

Repository: VladimirReshetnikov/ProveIt. Revision: `8188525b70033dcfe7c51ea5ae2c8723ad0c0198`.

The maintained branch already optimizes Euler characteristic over the full certified minimum-span face. This delivery adds a bounded-excess query and a different global lexicographic selector; it does not replace an allegedly incomplete root-sampling implementation.

## Recommended intake

Keep this package together in a descriptively named research/report directory assigned by intake. Do not select a fixed report number from a moving reports index. Initially use the standalone kernels and preserve the maintained fallback. No patch in this package changes production code.

The adapter assumes `Topology/UnknotRecognition/fast` and this package's `src` and `integration` directories are on PYTHONPATH (or that the caller otherwise makes `native_adapter.py` importable). It uses the inspected private `_euler_model`, `_prepare`, and `_coordinates` interfaces. Before execution, compare their signatures and source semantics to the pinned revision. The adapter is **NOT_RUN** in this delivery, not a tested native integration.

```python
from native_adapter import optimize_native

candidate = optimize_native(
    triangulation, local_heights, minimum_span_certificate,
    radius=2, max_work=5_000_000,
)

connected_candidate = optimize_native(
    triangulation, local_heights, minimum_span_certificate,
    lexicographic=True, max_work=5_000_000,
)
```

The normal coordinates and Euler number are candidate data. Both calls leave `knot_verdict` null.

## Source-bound verification requirements

The finite arithmetic checker accepts a height model. Before a knot verdict, independently authenticate the diagram-to-exterior construction; the orientable manifold structure and boundary torus; signed global edge coherence; normal matching and quadrilateral admissibility; and the primitive cohomology class. Raw edge gcd is not a substitute for integral primitivity after a tree gauge.

For band maxima, retain the general component/disc or annulus verifier. Aggregate Euler characteristic is insufficient, and a failure to find a disc in a returned maximizer does not exclude other discs in the band.

For the global two-network selector, a new source-bound checker may derive connectedness from Theorem 8.3 only after reconstructing the Euler edge objective from the authenticated geometry and replaying both networks. Reconstruct the entire F-optimal face from the first dual flow. Reconstruct the auxiliary upper/lower variables and all span constraints for the second solve. Check that the returned F and D equal the certified values. Then use the source-bound disc or annulus/capping path to finish the positive assertion. Do not trust the producer's `score2`, `span`, or assertion of a primitive class.

Do not copy a positive-excess potential into `normal-cocycle-span-v1` or `diagram-cocycle-disc-v1` and keep the old minimum-span witness. The old equality and connectedness proof will generally fail. A new certificate schema would need an independently reviewed native implementation; none is silently introduced here.

## Performance gates

First compare k=0 against the maintained full-face optimum. Next compare small k with exhaustive bounded normal-coordinate or potential fixtures whenever a complete bound is known. Compare the new global selector on the documented difficult unknot and trefoil regressions. Record true additions to coverage, unchanged results, total wall time, work exhaustion, source replay overhead, and full portfolio effects.

The package's 100 constructed solid-torus cases are positive geometric regressions, not a difficult-knot benchmark. Their minimum-face and lexicographic outputs all have Euler characteristic one, so there is no empirical coverage gain in that corpus. Abstract box-timing ratios must not be advertised as native speedups.

## Failure semantics and resource limits

Unsupported negative weights: reject the restricted optimizer. Infeasible stratum: reject that stratum only. Exhausted work: INCONCLUSIVE. Failed F threshold: INCONCLUSIVE for this sufficient stage. Failed candidate component check: no positive certificate, not a negative knot verdict. Existing exact fallback behavior remains unchanged.

The reference work counter is checkpoint instrumentation, not an exact Python bit-operation meter. Complete band logs have H(T,k) records and can be large. Use streaming when only candidate generation is needed; a streamed result without all records is not a complete replayable global-optimum certificate.
