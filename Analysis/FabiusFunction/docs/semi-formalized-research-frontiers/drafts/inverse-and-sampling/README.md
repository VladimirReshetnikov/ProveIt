# Inverse and sampling

The inverse function's frontiers and the sampling/deconvolution circle of
ideas, in three consolidated volumes and two retained standalone reports.

## `Inverse_and_Sampling_Frontiers/`

Consolidated (2026-08-28) from:

- **Part I** — *Inverse Frontiers for the Fabius–Rvachev System*
  (formerly `Fabius_Inverse_Frontier_Report_Source_and_PDF/`);
- **Part II** — *Dyadic Inverse Germs and Barnes–Rvachev Deconvolution*
  (formerly `fabius_frontier_dyadic_inverse_barnes_report/`);
- **Part III** — *Dyadic Self-Sampling, Alias Superconvergence, and
  Rvachev–Appell Deconvolution*
  (formerly `Fabius_Dyadic_Self_Sampling_Frontier_Package/`).

The member drafts were absorbed verbatim (labels, citation keys, and
asset paths mechanically prefixed per part; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

## `Dyadic_Comb_Frontiers/`

Editorially merged (2026-08-28) from the six dyadic-comb drafts of the
second and third waves — three on comb sums/quadrature
(`Fabius_Dyadic_Comb_Sums_Report_Package/`,
`fabius-dyadic-comb-sums-report/`, `fabius_dyadic_comb_report_final/`)
and three on global polynomial interpolation
(`fabius_dyadic_interpolation_report/`, `fabius_interpolation_report/`,
`Fabius_Rvachev_Dyadic_Interpolation_Report/`).  Because the six
sources largely re-derived one another's core results, this volume is a
true merge (unified notation, one statement per shared theorem with the
best proof, all source-specific material retained) rather than a
part-per-source concatenation.  A seventh, an eighth, and a ninth source were absorbed 2026-08-28 as the
Bernoulli-periodization section of Part I — the tenth-wave
`Fabius_Euler_Maclaurin_Report_Package/` (*Euler–Maclaurin and
Exhaustion Quadratures for Fabius and Rvachev Moments*): shifted
corrected rules for general polynomial weights, composite-mesh 2-adic
termination and reflection reduction, phase-modulated first-defect
series with Fabius-side forced phases, the first-harmonic proof that
D(2r) > 0 for every r (settling the volume's spectral-positivity
conjecture, and with it the odd half of the sharp-threshold
conjecture), the closed Ruffa exhaustion tail with derivative-free
rational Richardson extraction, the base-b termination dichotomy, the
composite-mesh Rvachev quadrature (sharp by the companion polynomial
volume's scale classification), and the Thue–Morse moment-identity
family; and its independently written eleventh-wave twin
(`fabius_rvachev_exhaustion_euler_maclaurin_bundle/`, *Exhaustion,
Euler–Maclaurin, and Spectral Exactness for Fabius–Rvachev Monomial
Integrals*), merged into the same section: the exact all-mesh alias–Bernoulli identity (layer cake +
Faulhaber, valid below every threshold), the general-q first defect in
Bernoulli-moment and spectral forms with midpoint/upper parity
superconvergence one level below threshold, the Bernoulli-moment
identity β₂ₘ = (−1)ᵐ·2(2m)!·D(2m)/(2π)²ᵐ (the twin's
conjectured sign law now follows from the positivity theorem; up to
sign these are the polynomial volume's defect values ℰ₂ₘ₋₁(0)),
the one-correction half-interval Rvachev rule with its
termination/one-mode exhaustion dichotomy and exact two-level
recovery, the supergeometric odd-base bound, and the q=1/4
Gaussian-binomial filter form; and the twelfth-wave Bernoulli–Ruffa
phase–resolution calculus, whose multiple-angle domination lemma
|Φ(qℓ/2)| ≤ |Φ(q/2)|/ℓ settles the twisted-positivity question
and BOTH phase-classification conjectures (the parity-forced phases
are the only superconvergent shifts, at every level and every odd
part), and which adds finite phase cubature (Simpson/Boole/Gauss in
the phase variable — exact moment certificates with no Bernoulli
correction), the phase–resolution separation principle,
Thue–Morse–Bernoulli digital phase filters with exact top-mode
constants and root-of-unity/digit-mask generalizations, coherent
radix exhaustion along tag orbits, anisotropic tensor shells, and a
proved all-orders complex-power expansion.  Provenance with SHA-256 hashes and the
deduplication record are Appendix E of the volume; every source's
supporting files live under its `assets/`.  The absorbed draft
directories are deleted; git history is the archive.

## `Inverse_Endpoint_All_Orders/`

Editorially merged (2026-08-28) from the three same-topic
inverse-asymptotics drafts of the fourth, fifth, and sixth waves:
`inverse_fabius_all_orders_package/` (*Closed All-Orders Endpoint
Asymptotics for the Inverse Fabius Function*),
`inverse_fabius_asymptotics_report/` (*Complete Small-Argument
Asymptotics of the Inverse Fabius Function*), and
`inverse_fabius_asymptotics_package/` (*Complete Small-Argument
Asymptotics of the Inverse Fabius Function* — the Wright-omega
write-up).  The first two both prove the closed Lagrange–Bürmann
coefficient formula, the universal highest logarithm, the explicit
third correction, and the elasticity recurrence — stated once, with
the independently derived third corrections verified algebraically
identical.  Contributions kept per source: structure laws (top-jet
transfer, Fourier/strip algebra, phase-locked tomography, derivative
hierarchy, exact-dyadic-quantile numerics); the
constrained-partition saddle engine and the exact 2-adic completion
of the Laplace exponent (dyadic Bose tail, Mellin bridge, exact
saddle map); and the log-free Wright-omega carrier (bounded periodic
coefficients with no logarithms, g₁ = −Ψ and the universal 5/24,
convergent bare skeleton, conditional Gevrey transfer, and
carrier-comparison numerics reaching 1.1e−9 at n = 160).
Complements — and imports the prior inverse corrections of —
`Inverse_and_Sampling_Frontiers/`.  Absorbed directories deleted;
provenance with SHA-256 in the volume's Appendix C and
`assets/SHA256SUMS-absorbed.txt`.

## `Inverse_Fabius_Computability_Report/`

Filed 2026-08-30 from `Inverse_Fabius_Computability_Report.zip` (689,198
bytes; SHA-256
`755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`).
The canonical 30-page A4/27 mm/Libertinus report gives self-contained
paper-level proofs of the least-interval-mass identity, exact inverse modulus,
elementary endpoint-mass estimate, tolerant-bisection realizer,
inverse-computability packaging, and optimal input-bit law.  Those results do
not yet have matching public Lean declarations.  The crosswalk separately
identifies the already formalized forward spline/computability, strict shape,
inverse identities/calculus, exact dyadic evaluation, and leading inverse
endpoint equivalent; explicit periodic and all-orders inverse reversion remain
frontier-document results.  The standard-library exact-rational supplement
reproduces its captured output byte for byte.  Original five-file hashes are
preserved in `ARRIVAL_SHA256SUMS.txt`; the current six-entry
`SHA256SUMS.txt` verifies 6/6.

## `inverse_fabius_iterates_nowhere_analytic/`

Filed 2026-08-30 from `inverse_fabius_iterates_nowhere_analytic.zip`
(1,137,032 bytes; SHA-256
`8b1c05d59e120ecd20d69cd5aeb0009639f2b3b9a6c9fef32bdf82270eee16bd`).
This canonical 24-page A4/27 mm/Libertinus inverse-iterate companion derives
nowhere analyticity and formal-radius transport from the corrected forward
iterate report, then proves the affine but nonrepresenting center jet and the
iterated endpoint obstruction.  The inverse-nowhere-analytic conclusion is
already a corollary of that forward report and is not independent novelty.
Lean status is limited to the existing one-fold inverse analytic locus and
one-fold endpoint Hölder obstruction; the higher iterates, formal-radius
transport, all-order center jet, and iterated endpoint scale remain
manuscript-only.  The hostile audit retains 19 nonconjectural labelled results,
quarantines three stale, false, or duplicate conjecture claims as warnings,
and leaves only two explicitly unformalized conjectures. The pinned numerical
replay reproduced all 7 generated outputs byte for byte before repository LF
normalization; it proves none of the analytic claims. The submitted 13-entry arrival ledger is preserved as
`SHA256SUMS.arrival.txt` and verified 13/13 before normalization; the current
15-entry `SHA256SUMS.txt` verifies 15/15.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and previous paths.
