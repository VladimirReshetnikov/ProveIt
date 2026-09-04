# Repository and claim-status audit

Audit date: 30 August 2026. This record distinguishes the submitted artifact, the current
normalized package, current Lean inputs, and paper-only frontier claims.

## Arrival and normalization provenance

- Arrival archive: **fabius_frontier_report_2026.zip**, 803,598 bytes.
- Arrival SHA-256:
  **afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e**.
- Arrival Git blob: **ec8727448efff206724963f5b3922ff5b8f5fc61**.
- Intake commit: **7d6527058f0325fd509dc0b54bac8e8625843a36**
  (“Intake q-parameter response and dynamics report”).
- Archive structure: one wrapper directory; 18 entries comprising 14 files and four
  directories; 909,799 uncompressed bytes. No traversal path, symlink, encryption, duplicate
  name, or case-fold collision was present, and every CRC check passed.
- The archive’s 13 payload checksums all verified. **ARRIVAL_SHA256SUMS.txt** preserves that
  ledger verbatim. The first repository normalization changed only CRLF to LF in five CSV
  files; its 13-row ledger also verified.
- **SHA256SUMS.txt** was the separate exhaustive normalized-package ledger. It
  was retired repository-wide on 2026-09-01, and its historical bytes remain
  recoverable from Git history.

## Hostile claim audit and disposition

1. **Conditional velocity versions.** A regular conditional expectation is defined only
   modulo the law of \(X\). The report now states the flux and oddness pointwise only for the
   canonical smooth representative \(b_*=-G/f\); every other version agrees with it
   Lebesgue-a.e. on \((0,1)\), and its continuity equation is distributional.
2. **False Fourier small-divisor suggestion.** The candidate in the submitted discussion
   simplified to a constant rather than a small divisor. It has been withdrawn; no multiplier
   is asserted before a derivation converting the lower-Lambert phase to the dynamical phase.
3. **Susceptibility source and KR basepoint.** The source is now first defined as the finite
   zero-mass smooth-density measure \(\sigma_q=\nu_q-R_q\nu_q\), with the derivative action
   stated for compactly supported \(C^1\) tests. The contraction proof subtracts
   \(T_q\phi(0)\), which is legitimate because the input measure has zero total mass.
4. **Higher response.** Only the Leibniz hierarchy in distributions is unconditional. The KR
   inverse at order \(s\ge2\) is conditional on independently representing the differentiated
   source as a finite zero-mass measure; no such common-space theorem is claimed here.
5. **Koenigs linearization.** The submitted telescoping sketch did not establish the
   all-orders derivative majorants required for \(C^\infty\) convergence. This is now
   hypothesis (K), not a proved lemma. The global \(\Theta\), inverse-iterate asymptotic,
   nonanalyticity, escape clock, periodic quotient, and dependent conjectural discussion are
   all marked conditional on (K).
6. **Endpoint height.** Compact-uniform convergence is now justified by Dini’s theorem;
   positivity separately excludes \(B<0\) and \(B=0\); and the right-endpoint formula is
   written explicitly for \(1-F^n(x)\).

## Exact Lean-input crosswalk

All paths below are under **Analysis/FabiusFunction/Lean/FabiusFunction/**.

| Paper input | Current formal source |
|---|---|
| Geometric law, affine self-similarity, reflection, support | **GeometricUniformLaw.lean** |
| Fixed-\(q\) CDF/density and spatial smoothness | **GeometricUniformCDF.lean** |
| Half-base Fabius and Rvachev identifications | **ProbabilityRepresentation.lean** |
| Fixed-parameter prefix sinc convergence | **GeometricSincFactorization.lean** |
| Affine independent-copy operator and uniqueness | **AffineIndependentCopy.lean** |
| Diagonal/shape inequalities | **Convexity.lean** |
| Smooth interior inverse and positive derivative | **FabiusInverse.lean** |
| Exact midpoint transfer and jets | **MidpointEndpointTransfer.lean** |
| Inverse midpoint offset/defect identities and oddness | **InverseMidpointDefect.lean** |
| Endpoint small-o flatness | **FabiusFlatness.lean** |
| Leading quadratic logarithmic endpoint law | **FabiusLogSquaredAsymptotic.lean** |
| Cumulant/Bell/geometric-uniform algebra | **CenteredMomentCumulants.lean**, **ExponentialBell.lean**, **GeometricUniformDictionary.lean** |

The named bridge theorems
**geometricUniformDistribution_selfSimilar**,
**geometricUniformCDF_one_half_eq_fabiusReal**, and
**geometricUniformDensity_one_half_eq_rvachevUp** occur in those sources. The fixed-\(q\)
theorems **contDiff_geometricUniformCDF** and **contDiff_geometricUniformDensity** do not
formalize joint parameter–space differentiability.

## Formalization and novelty boundary

No new theorem in this report has an exact current Lean counterpart. In particular, the Lean
tree does not yet contain joint \(q,x\) smoothness, the flat fronts, parameter tangent and
resolvent/refinement theory, response sinc/cumulant/moment/Legendre formulas, higher-response
source regularity, hypothesis (K), global \(\Theta\), endpoint \(B\), or the dynamical periodic
factor.

The static central-plateau result and generic Bernoulli-cumulant/Bell infrastructure overlap
the existing **Fabius_Rvachev_Frontier_Report** and the consolidated
**Exponents_and_q_Series_Frontiers** volume. The parameter derivatives and flat moving-front
conclusions are the distinct contribution here. Existing forward/inverse-iterate reports
overlap the topic of iteration but do not supply the claimed global Schröder coordinate.

Accordingly, “repository-novel” is only a scoped corpus-search result, never a literature
priority claim. Paper proofs remain paper proofs; the table above lists dependencies, not
formal counterparts of the new results.
