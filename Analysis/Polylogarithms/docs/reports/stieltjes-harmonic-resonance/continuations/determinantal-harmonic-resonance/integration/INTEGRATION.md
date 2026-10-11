# Proposed integration

## Destination

A suitable standalone report directory is:

`Analysis/Polylogarithms/docs/reports/determinantal-harmonic-resonance/`

The delivered directory is self-contained. No repository write, patch,
archive retirement, or canonical integration has been performed.

## Review order

Start with Section 2 (Gamma product), then Section 3 (largest-index
normal convergence and the cutoff/spectral distinction), Section 4
(Stieltjes jets and primitives), and Section 6 (the independent rank-one
harmonic argument). Sections 5 and 7 supply exact applications. Section 8
records audit scope, Section 9 further questions, and Appendix A the
replay boundaries.

## Thematic mapping

| Delivered source | Suggested thematic link |
|---|---|
| `sections/02-determinant.tex` | Gamma-generated harmonic sums and determinant methods |
| `sections/03-resonance.tex` | First-resonance Gamma calculus; compare the existing `07-mixed-dougall-identities.tex` |
| `sections/04-stieltjes.tex` | Hurwitz/Stieltjes integration and differentiation |
| `sections/05-harmonics.tex` | Multi-index extension of Gauss harmonic coefficient identities |
| `sections/06-depth-two.tex` | Harmonic sums, depth reduction, and cyclotomic coordinates |
| `sections/07-explicit.tex` | Exact identity collection and reproducible experiments |

This is a proposal for a separate analytic integration pass, not a claim
that these files may be inserted without editorial work. Their proofs
must travel with their statements. All labels start with `dhr:`. The
standalone preamble declares standard macros such as `\Li`, `\Q`, and
`\Bell`; reconcile them with the canonical preamble rather than blindly
copying duplicate definitions.

## Do not promote unrelated claims

The report neither resolves S6/S8 nor proves actual period independence,
minimal depth, or any theorem-prover declaration. The all-rank rational
simple-pole theorem does not automatically cover repeated poles,
unrelated rational grids, or higher resonances. The incoming binary
archives were not analytically audited here.

The Gauss–Vandermonde evaluation uses classical methods and is not given
a global-novelty claim. The research contributions to review are the
precisely normalized largest-index subtraction, its all-order Stieltjes
transport, the rank-one harmonic support theorem, the depth-two closure,
and their explicit consequences.

## Normalization checkpoint

Before importing any finite-part row, identify its normalization:

- hard cutoff at maximum index N;
- spectral Laurent finite part;
- Abel constant of the generating function;
- ordinary bracket subtraction at point alpha.

For this family the hard-cutoff constant is the spectral finite part
minus A'(0). In the canonical r=2 normalization the spectral finite part
is -1/3, the hard-cutoff constant is (gamma-3)/4, and the subtraction value
at alpha=1 is -3/4. They must not be relabeled as one another.

## Replay

Preserve the delivery records, run both verification scripts on a copy,
and build the article with `build.sh`. The outputs distinguish finite
exact assertions from non-interval floating-point diagnostics. A passed
suite does not substitute for the analytic normal-convergence proof or
for visual review after a changed LaTeX build.
