# Source audit and proof-status boundary

Audit date: 11 October 2026. This is a targeted comparison, not a complete
proof audit of the repository or a claim of exhaustive literature priority.
No repository files were modified.

## Repository material actually inspected

Repository: `VladimirReshetnikov/ProveIt`.

1. `Analysis/Polylogarithms/docs/manuscript/README.md`.
   Retrieved again at commit
   `e3d7ec5d3f9be259c1f91edaea4389f4e79b5b03`, lines 1–180.
   Returned blob SHA: `dc0fa26d0e5c2ede56df37c5640c7319681dfd25`.
   Confirms the multi-volume structure, experimental/proof distinctions,
   and conjectural status of S6 and revised S8. It contains the editorial
   duplication described below.

2. `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/stieltjes-harmonic-identities/sections/harmonic.tex`.
   Returned text was read in ranges through line 490. Returned blob SHA:
   `51108e8519d46af87dc3682956511fc525cecec3`.
   Relevant distinction: the constant-term Gamma formula does not determine
   every mixed harmonic–Stieltjes coefficient R_{r,k}. This article does not
   evaluate that different family.

3. The same continuation's `sections/further_research.tex`.
   Returned blob SHA: `1051d5c4348e9b697712468e9c6b0c0f4d6373db`.
   Used to delimit the still-open mixed-coefficient and Gaussian-period
   questions, not to relabel our ordinary Stieltjes moments as their solution.

4. `Analysis/Polylogarithms/docs/manuscript/chapters/07-mixed-twist-identities.tex`.
   Returned blob SHA: `3c8c6e6cb22f6a72391983301abf1958cc422dcd`.
   The Dirichlet-mixture and integer-resolvent results concern a different
   twist-convolution problem. They were not re-proved as a new contribution.

5. `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/mellin-lerch-dilation/sections/03-jets.tex`.
   Retrieved at commit `64c0a386f5eb0cfc7e1ebb751b46eaed20f3f84a`.
   The returned content was truncated near its end; the displayed Gamma,
   Stieltjes, canceled-Pochhammer, and primitive sections were inspected.
   Its integral variable is a polylogarithm argument. The present theorem is
   a Mellin integral in the positive translation x of gamma_n(x+a).

6. Targeted connector searches for Stieltjes, Bernoulli, Mellin, moments,
   mixed frequency, and simplex topics. Results included harmonic-shift-
   moments, harmonic-gaps-mixed-moments, beta crossing, and vertical reports.
   Search snippets were used only to locate or distinguish directions;
   they were not treated as complete proofs or complete source audits.

The repository changed during retrieval. The two recorded commits and
individual returned blob identifiers should not be described as a single
frozen checkout. The final README re-fetch independently confirmed the
specific editorial finding.

## Incoming material: inventory only

The `docs/incoming` directory listing was inspected. It showed, among others,
archives titled Bernoulli Tails and Spectral Faces, Higher Spectral Defects,
Vertical Lattice Jets, Bilinear Tails and Determinants, and Higher Quadratic
Jets. The binary interiors of those archives were not inspected in this
session. Connector access returned directory metadata, while attempted
container retrieval was unavailable. A limited Library search did not supply
those interiors. No claim is made that this report is disjoint from every
unexpanded archive; checking them is an integration prerequisite.

## Verified editorial correction

In the pinned README, the paragraph describing the complete 1,032-input
first-letter X family, top-sector rank 1,008, and kernel dimension 24 occurs
twice consecutively. Retain one copy after checking the current version.
This is not a mathematical correction to the rank claim. A context-sensitive
note is supplied instead of an automatically applied patch.

## No attributed mathematical error established

No mathematical error was established in the specific inspected harmonic
constant-term, mixed-coefficient warning, or Mellin formulas relied upon for
comparison. The paper's cautions about divergent separated summands,
zero-times-pole limits, and elementary versus complete harmonic coefficients
are proved warnings, not accusations that an inspected source made them.

## Literature and originality

Classical inputs are credited in the article: the beta integral, Hurwitz
Euler–Maclaurin expansion, Gamma recurrence/reflection and Taylor formulas,
Bernoulli special values, Hurwitz's Fourier formula, and cutoff Mellin
continuation. Directly consulted public primary/official resources include:

- NIST DLMF, sections 25.11 and 25.12, and Gamma/polygamma material.
- Don Zagier, *The Mellin Transform and Related Analytic Techniques*,
  author-hosted PDF, especially pages 1–3 (including rendered page inspection).

The specific balanced all-order formulation, uniqueness statement, moment
criterion, and coefficient organization are proposed additions for review.
Neither publication priority nor arithmetic independence is certified.
The generalized R_{r,k}, S6, and revised S8 questions remain unresolved here.
