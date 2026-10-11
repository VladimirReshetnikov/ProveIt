# Targeted audit and claim boundaries

## Question resolved

The selected `shifted-hurwitz-jets/sections.tex` asks whether products of
three separated Stieltjes factors admit an all-index representation by
colored Tornheim or multiple Lerch jets, and singles out a fully
regularized three-digamma formula at distinct rational shifts.

Theorems 4.1–4.2 and 5.1 provide that representation at arbitrary separated
real shifts, with explicit normalization. Equations (4.7)–(4.8) and Section
5.1 specialize it to three digamma factors. This is a representation
result, not a proof of a smaller transcendental basis.

## No invented source erratum

No false theorem was identified in the selected canonical passages.
The current manuscript's pointwise derivative identities, its attribution
of the classical cubic log-Gamma formula, and the proved status of S4
are retained. The study did not audit all 446 manuscript pages or all
incoming archives.

The proposed update is to the research-status paragraph. The following
items are safeguards for integration, not assertions that the inspected
manuscript presently contains these errors:

1. **Zero Fourier mode.** The normalized family at zero is delta minus
   one, not delta. The six-sector kernel has value 2 at (0,0,0).
2. **Endpoint constants.** The finite constant in the Mellin functional
   and the even-index zeta correction in the Stieltjes–cotangent transform
   must be preserved. In particular, I_0(1/2) = -pi^2/2.
3. **Discrete versus analytic orders.** The integer partial-fraction
   reduction of Tornheim sums cannot be differentiated in an integer
   index as though it were an analytic identity in that index.
4. **Derivative contacts.** Periodically extending first and then
   differentiating differs from taking the raw finite part of a pointwise
   derivative. The correction is explicitly elementary-harmonic.
5. **Separated versus colliding singularities.** Generic Stieltjes
   products require distinct shifts. Ordinary primitive products admit
   coincident shifts for a separate convergence reason.
6. **Reflected versus one-sided extensions.** Symmetric cotangent
   principal values and one-sided Stieltjes finite parts use different
   local conventions. The article specifies both.

## Computational safeguards established during development

An early implementation integrated a complex polylogarithmic Mellin
integrand to a formal infinite endpoint. Extreme quadrature nodes caused
an mpmath memory failure through an unnecessarily tiny exponential argument.
The delivered positive-integer Mellin checker instead uses a finite upper
cutoff and an explicit exponentially decreasing tail estimate. This is a
finding about the newly written checker, not a demonstrated flaw in a
repository theorem or its historical computation.

Polylogarithm order derivatives at zero are evaluated by convergent local
and exponential series, with rational-boundary Gamma checks. The delivered
checker avoids infinitesimal black-box differentiation in that variable.
The output is not claimed to be interval certified.

## Claims not made

- No proof of S6 or the revised S8 special-value conjecture.
- No period independence or minimum transcendental depth.
- No general collision or path-independent triple renormalization law.
- No proof-assistant formalization or external peer-review certification.
- No exhaustive numerical evaluation of the high-index or full derivative
  triple families.
- No global novelty claim for classical Fourier, Gamma, integer Tornheim,
  or individual rational specializations.

The archive is a proposed research contribution. Preservation, successful
replay, and acceptance into the canonical manuscript are separate steps.
