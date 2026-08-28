# Inverse and sampling

The inverse function's frontiers and the sampling/deconvolution circle of
ideas, in two consolidated volumes.

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
part-per-source concatenation.  A seventh source, the tenth-wave
`Fabius_Euler_Maclaurin_Report_Package/` (*Euler–Maclaurin and
Exhaustion Quadratures for Fabius and Rvachev Moments*), was absorbed
2026-08-28 as the Bernoulli-periodization section of Part I: shifted
corrected rules for general polynomial weights, composite-mesh 2-adic
termination and reflection reduction, phase-modulated first-defect
series with Fabius-side forced phases, the first-harmonic proof that
D(2r) > 0 for every r (settling the volume's spectral-positivity
conjecture, and with it the odd half of the sharp-threshold
conjecture), the closed Ruffa exhaustion tail with derivative-free
rational Richardson extraction, the base-b termination dichotomy, the
composite-mesh Rvachev quadrature (sharp by the companion polynomial
volume's scale classification), and the Thue–Morse moment-identity
family.  Provenance with SHA-256 hashes and the
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

See [`../MANIFEST.md`](../MANIFEST.md) for titles and previous paths.
