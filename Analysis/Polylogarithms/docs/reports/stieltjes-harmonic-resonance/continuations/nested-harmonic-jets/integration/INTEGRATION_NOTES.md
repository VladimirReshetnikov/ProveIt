# Integration notes

## Pin and package scope

This delivery was prepared against ProveIt revision
`fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`.

It is one standalone research article, not an instruction to modify or delete any existing incoming archive. No repository mutation was performed. Follow the repository's current incoming procedure at intake rather than assuming this delivery itself completes that procedure.

Suggested thematic placement: a new report in the existing `Analysis/Polylogarithms` research-report structure, named for nested harmonic spectral jets. Reconcile that location with the actual current report index when integrating. Do not invent or overwrite an existing report directory based only on this suggestion.

For chapter integration, the natural links are:

- Integration: the precisely normalized ordinary and Euler primitives in Section 8.
- Differentiation: the Gamma-valued spectral family, Bell jets, regulator conversion and distribution identities in Sections 3–7.
- Depth: the all-depth generating function, polynomial classification and bounded-nesting theorem in Sections 9–11.
- Discovery/research programme: the unresolved questions in Section 13, with no change to the S6/S8 status based on this paper.

Use a unique label prefix such as `nhj:` when importing statements into the combined manuscript. `G_N`, `F_r`, `T_m`, `P_m^*`, and `L_{j,n}^{(m)}` are local notations and should be checked for collisions.

## What is actually new work in this package, and what is not claimed

The package derives and proves an all-order system of regulator-conversion and resonance identities, including the higher-genus cyclotomic product and the all-order zero-factor Bell formula. The classical reciprocal-Gamma product, Newton identities, equal-order-one polylogarithm generator, and established multiple-zeta regularization framework are credited. The exact worldwide novelty of every formula has not been established.

This is not another delivery of shifted bilinear Stieltjes correlations or circular Gamma convolutions. The five incoming archives at the pin already cover that direction. Here, resonance means a zero in a finite depth-generating product. It is not the positive-integer Lerch resonance in the earlier incoming report.

## Proof obligations that must travel with extracted statements

1. The base parameter is real `a>0`; the powers `(n+a)^s` use the real logarithm of that positive base. More general complex-parameter branch statements have not been proved here.
2. The genus-one product converges for `Re(s)>1/2`, and genus M for `Re(s)>1/(M+1)`. The all-depth polylog generator is entire in its depth weight only in the stated region `Re(s)>0`, `|w|<1`.
3. Spectral derivatives of `Li_{s,...,s}` are simultaneous diagonal derivatives of all orders, not derivatives in only the first index.
4. Harmonic cutoff coefficients, diagonal Laurent finite parts, and Abel normalization are different. Keep the exact counterterm, the double factorial in the conversion law, and the multiplication exponential.
5. `G(1,z)=Gamma(a)/Gamma(a+z)` does not justify setting its spectral derivative to zero at a reciprocal-Gamma zero; keep the zero-flow/cancellation argument.
6. The higher-order depth bound concerns shifted logarithmic Euler sums as explicitly defined, not minimal classical polylogarithmic depth or period independence.
7. Endpoint cancellation is for the convergent largest-index series; individual all-ones depth terms at `w=1` may be divergent.
8. The first-order elementary formula does not prove that all higher spectral derivatives are elementary.

## Targeted audit

The main manuscript and relevant portions of four chapters were inspected, along with the incoming inventory/intake instructions and README excerpts for all five archives. The incoming archives' full TEX manuscripts and check outputs were not all audited. `sources.json` records this limit.

The integration chapter's wording that comparison atoms “must be Q-independent” should be replaced with the more precise wording in `proposed_editorial_correction.md`. This issue had already been flagged by other incoming work; it is explicitly not claimed as newly found here. No executable patch is supplied, because the correction should be reconciled with the current combined manuscript and earlier pending proposals on intake.

## Evidence status

There are ordinary mathematical proofs, 826 finite exact assertions, and 1,075 floating-point comparisons at 60 decimal digits. No Lean formalization, independent peer review, interval certification or exhaustive novelty audit has been carried out. The included checks are reproducible and are not substitutes for the analytic proofs.
