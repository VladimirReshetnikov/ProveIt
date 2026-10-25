# Proposed ProveIt intake

Suggested new contribution name: `reciprocal-pooling-integral-projections`.
Place additively under the existing DiophantineConsistency research collection,
retaining the 225-variable source and all older alternatives.

## Suggested catalog entry

**Reciprocal pooling and integral projections (25 October 2026).** Direct
C222 quartic in 218 unrestricted integers / 155 quadratic residuals / 34,984
collected monomials / coefficient height 113,304; degree-ten companion in 215
integers / 152 residuals / 99,914 monomials / height 113,304. Seven exact integral
projections compose the pooled-power225 parent with common-Hessian and affine
methods. A new two-base reciprocal error-sum theorem merges the q and q+1 power
pools with no coprimality assumption. Larger expanded support is an explicit
tradeoff. Ordinary ZFC-formalizable proof composed with the retained calibration;
no new full Lean/Rocq replay or global minimality claim.

## Review order

1. Read the report's exact definitions and comparison table.
2. Inspect the new reciprocal-pooling theorem and its bootstrap, including unit
   bases, signed indices, common sign, and the clearing factor.
3. Run `python3 -B verify.py --rebuild` in a fresh extraction.
4. Inspect the independent mathematical and finite reviews in `proofs/`.
5. Check `provenance/SOURCES.json`, parent hashes, and inherited calibration.

The final quartic and decic residual files have SHA-256:

```text
quartic218 878d2f427a117f35b4c211a223003978d52509acc46a5c97b829380b6e608ad8
decic215   a335e0d1d1d82aa2cd30c2f436ed61a752fff001db134b339c23fae01d4a70b0
```

The static 669-row-operation certificate protects the final four pool rows.
Do not substitute the earlier 670-operation experimental chart: its one altered
pool row has a different literal companion and a different coefficient count.

The inherited source tree may be deduplicated at intake only with a retained
exact path/hash mapping and a portable reconstruction of all required files.
The complete final equations and the new verifier should remain directly
available.
