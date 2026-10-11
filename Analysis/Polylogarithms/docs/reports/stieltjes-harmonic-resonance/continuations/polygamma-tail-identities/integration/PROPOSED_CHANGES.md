# Proposed integration changes

Baseline: ProveIt commit `f7e35be357654198c1546fd40f363694c5bcc2cc`.

## Recommended new incoming report

Add `ProveIt_Polygamma_Tail_Identities_2026-10-11.zip` as a new report,
preserving its PDF, source, exact data, and verification records.
Its claims build on the six existing incoming archives; the supplied
`incoming_audit_summary.json` distinguishes that baseline from this continuation.

## 1. Recorded Gaussian Family-2 example

File: `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`.

Target: `double:eq:fam2-example`.

Attach the direct proof and the simplified identity from the new article's
`bip:eq:family2-short`, with component evaluations `bip:eq:12` and `bip:eq:21`.
The original integer-relation discovery can remain as provenance; the
equation now has an analytic proof. The exact comparison with the original
right-hand side is included in the new article.

The underlying parity theorem is established work of Nakamura and Panzer.
The Gaussian height-one value used in the comparison is already in the
canonical manuscript (Proposition 1.12's following unnumbered specialization,
or Theorem 4.12 / `gaussian:eq:parity-A`). The new article includes a short
self-contained Nielsen proof to avoid an ambiguous unnumbered reference.

Do not revive or newly “correct” the older general nonreduction wording:
the current pinned source already contains that historical correction.

## 2. Optimal consecutive tail moments

Incoming archive: `ProveIt_Canonical_Digamma_Fifth_Moment_2026-10-11.zip`.

Targets: `sections/09_questions.tex`, `conj:firstq`, and its claim ledger.

Add the new theorem for every `p=q-2>=2`, citing `adj:main` and
`adj:determinant`. The proof supplies a positive recurrence and a nonzero
determinant for the entire family. The diagonal case and isolated examples
such as `(2,6)` were already treated in the source. The uniform assertion
for general gaps at least four remains open.

Retain the source interpretation of rank: rational coefficient rank in a
formal coordinate space. Do not replace it by a claim of independence of
actual special-function constants.

## 3. Higher digamma moments and the sixth calculation

Attach `sixth:main` / `sixth:Q6` to the incoming higher-moment research agenda.
The full sixth moment is explicit in height-one Laurent slopes and Omega_5.
Omega_5 has an absolutely convergent logarithmic series, an exact value of
its generating function at zero, and the 17 individually convergent MZV
germs in Appendix A.2.

The remaining question is further arithmetic reduction of this specified
coordinate. Neither its irreducibility nor independence is asserted.
The generic all-power algorithm and the fifth moment predate this continuation.

## 4. Reusable additions

- Gamma coefficient sectors: `nfsector:squares`, `nfsector:trigamma`.
- Quadratic Hurwitz products and all jets: Section 5, `hprod:all-jets`.
- Generalized Stieltjes derivative correlations: `hprod:stieltjes-products`.
- Derivative-containing polynomial spectral theorem and primitive:
  `spectral:ML`, `spectral:primitive`, `spectral:depth`.

Credit the abstract normal-form decomposition to Guo–Regensburger–Rosenkranz,
Proposition 4.10. Credit the classical Hurwitz product kernel to the cited
Mikolás literature. Preserve the original-coordinate correction when
specializing that meromorphic kernel to integer orders.

## Audit limitations

All six archive inventories and relevant status material were examined, with
targeted proof checks. No new false inherited theorem was established.
The source report’s external-paper corrections remain attributed to those
earlier reports. Gaussian S6, revised S8, higher golden candidates, general
larger-gap tail families, and further mixed-coordinate arithmetic reductions
are not marked solved.
