# Proposed ProveIt integration

## Baseline

Repository: VladimirReshetnikov/ProveIt.

Pinned baseline: 36edefa8c531d9d6df8306ac51bcc317250f404c.

The package is an independent research continuation. No repository write or push was performed. Reconcile against later commits before editorial integration.

A suitable new report directory is:

    Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/lattice-contacts-mixed-zeta/

The complete ZIP can also be placed in docs/incoming/ as a new report.

## Suggested manuscript routing

| Contribution | Recommended relation to existing material |
| --- | --- |
| All lattice contacts and periodic filters | Follow the Vertical Lattice Jets report's compensated sampling theorem; answer its Questions 1 and 6. |
| Modular order transport | Extend Vertical Lattice Question 7 with the stated a = 1 restriction. |
| Arbitrary mixed even tails | Follow the repeated-tail section in Bernoulli Tails and Spectral Faces and the earlier mixed bilinear moment theorem. |
| Independent Stieltjes shifts | Extend the material near chapters/07-shifted-stieltjes-correlations.tex; record Tail Kernels R8 as resolved in the explicit convergent class. |
| Gamma collision coefficients and faces | Follow the existing common-ray spectral-face section. Keep the inherited normalization unchanged. |
| Joint spectral-order obstruction | Place before any new use of independent mixed derivatives; retain its local rational subtraction. |
| Cutoff-coordinate conventions | Cross-reference the manuscript's Stieltjes contact and dilation-contact sections. |
| Research-status corrections | Update the research ledger and source-correction appendix, with the original source credited. |

## Labels and macros

The new tail labels use the prefix mtp:, independent-shift labels use gs:, and face/joint-spectrum labels use sfj:. The root lattice/modular labels use thm:, lem:, cor:, and eq:; these should receive a report-specific prefix if merged into a larger document with a colliding label namespace.

The shared preamble defines Li, Log, FP, Ree, ii, dd, C, N, Q, and R. Reconcile these with the manuscript preamble rather than defining them twice. The independent-shift fragment has eight private gs-prefixed macros.

The bibliography contains 15 entries. Several agents' duplicate DLMF and predecessor citations have already been consolidated into one key per source.

The mixed source file uses the superscripted integration operator I^q, while the spectral source uses a subscripted face operator I_k. Both are defined locally. If global manuscript notation requires a different integration symbol, rename only the mixed primitive notation consistently.

## Exact ledger correction

Tail Kernels R7 is still listed as a target in that archive, but the Bilinear Tails and Determinants archive already resolves it in sections/04_cutoff_jets.tex.

Proposed replacement:

> R7: resolved by the all-order cutoff continuation in Bilinear Alternating Tails and Harmonic Determinants, Section 4. Cite cut:normal, cut:contacts, and cut:translation. Preserve the stated cutoff coordinate and the order-zero contact; the Gamma specializations are cut:Gamma and cut:Gammasquare.

This is a source-status correction. It is not a claim of a false theorem in the resolving report, and the inherited alternating formulas are not new results of this package.

## Scope that must survive editing

- The modular transport proved here is for horizontal shift a = 1 near the indicated order centers.
- The mixed recurrence covers all regular centered moments. It does not prove the separate arbitrary unequal bilinear optimal-prefix conjecture.
- Six- and eight-coordinate determinants establish formal-coordinate reconstruction, without asserting arithmetic independence.
- The independent-shift master is an explicit geometric-series evaluation. Generic finite classical-polylogarithm reduction is not claimed.
- Periodic zero-mean lattice sums are generally conditional. Additional horizontal differences give absolute convergence.
- The Gamma face formula with one displaced mass is ordinary and valid for every nonnegative displacement, not only near zero.
- Independent spectral orders need the displayed polar classification or explicit local subtraction; common-ray regularity is insufficient.
- The Gaussian S6 and revised S8 candidates remain conjectures. Existing high-precision residuals are not promoted to proofs.

## Verification files

Retain the six programs and their JSON results with the report. They are organized to be runnable outside the full repository and contain no external service dependencies.

The exact mixed-tail program includes both an unreduced-MZV comparison and independent finite summation by parts, an exact Laurent-polynomial telescoper, rational coordinate matrices, determinants, and the rational sum certificate.

The article's last section contains twelve research questions. Preserve these as distinct targets rather than replacing the already resolved predecessor entries with broad unspecific questions.

