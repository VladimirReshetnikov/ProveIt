# Claims and validation ledger

## Research target

Repository: VladimirReshetnikov/ProveIt.
Snapshot: `1085b506d65e207a05b7e9c861bb1fe88432fe38`.
Immediate predecessor:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Critical_Pressure/article.tex`.

The predecessor explicitly asks for the terms beyond the leading square root
and for normalized eigenvectors/equilibrium measures. Those questions, not the
already proved leading cusp, are the targets.

## Main claims and proof locations

| Claim | Article location | Status |
|---|---|---|
| Logarithmic and linear critical coefficients with remainder O(delta^(3/2-eta)) | Theorem 2.1; Sections 4–6 | Ordinary mathematical proof supplied |
| Exact all-base finite-part response constants | Proposition 5.2 | Ordinary mathematical proof and high-precision diagnostics |
| Exact binary finite-part identity | Corollary 5.3 | Ordinary trigonometric/integral proof and numerical check |
| First normalized right and left eigenvector corrections | Theorem 2.2; Section 7 | Ordinary norm/duality proof supplied |
| Right boundary layer on spatial scale sqrt(delta) | Theorem 2.2; equation (8.14) for detuning | Ordinary proof supplied |
| Half-atomic, half-Lebesgue critical selection | Theorem 2.2; Sections 7 and 9 | Ordinary proof, including variational interpretation |
| Explicit mixture selection for bounded detuning | Theorem 2.3; Sections 8–9 | Ordinary proof and collocation diagnostics |
| Exact leading amplitude constant | Corollary 7.1 | Consequence of normalized spectral projection |
| Critical equilibrium segment | Proposition 9.2 | Ergodic/entropy argument supplied |

## Previously established in the repository; not new claims here

The leading square-root pressure, the size-two atomic Jordan block, and the
leading bounded-detuning spectral/finite-size crossover are credited to
`Thue_Morse_Critical_Pressure`. The supercritical and all-subcritical leading
responses are also credited to their respective predecessor packages. The
Jordan foundation is reconstructed to make the normalization and dependencies
of the new coefficients explicit.

## Important normalizations and restrictions

- The transfer operator is the sum over b inverse branches, with no 1/b factor.
- The exponent s=1 is q=1/2 in the binary potential log cos^2(pi(x-c)).
- EulerGamma denotes Euler's constant, not the Gamma function.
- The refined remainder holds for each fixed 0<eta<1/2; its constant is not
  made explicit and is not uniform as eta approaches zero.
- Eigenvector expansions use C^alpha and its dual, with 0<alpha<1/2.
- Xi is a convergent finite-part functional on Holder functions, not a finite
  signed measure on continuous functions.
- Equilibrium limits are weak limits, not total-variation limits.
- Detuning uniformity is on each fixed compact set of u, not on unbounded u(t).
- The amplitude result takes n to infinity at fixed c first. It is not a new
  joint finite-size limit theorem.

## Computational validation actually performed

The supplied run uses 70 decimal digits for special-function checks; bases
2, 3, 5, and 7 test the two Jordan identities and the exact response identities.
The finite-part constants are compared with high-precision quadrature.
Two binary cutoff-integral checks test the closed trace formula.
Eight pressure collocation cases and one doubled-grid check are recorded.
Six left/right eigenvector cases test equilibrium selection via a cosine
observable. The raw JSON records actual residuals and package versions.

These are not interval computations. Small finite-matrix residuals do not
bound interpolation error or certify the spectrum of the continuum operator.
No proof of an infinite statement is inferred from a finite sample.

## Formal and novelty status

No Lean or Rocq files are supplied and no proof-assistant verification was
performed. The article is an unrefereed research draft. The targeted source
search did not establish unrestricted worldwide priority. A stronger priority
claim is deliberately not made.

## Open boundaries

The complete critical expansion, the sharp next logarithmic polynomial,
unbounded detuning, two-point phase regularity, convergence rates for selected
measures, the left boundary-layer profile, and formal/interval certification
remain research tasks. See the nine questions in Section 11.

## Editorial note (ProveIt, 2026-09-29)

The row "Exact leading amplitude constant | Corollary 7.1" is not new: the
predecessor `Thue_Morse_Critical_Pressure` already states the same
asymptotic for its eigenprojections (its `eq:critical-amplitudes`). What
this package adds is the derivation from the normalized eigenvectors; an
editorial note after Corollary 7.1 in `article.tex` says so.
