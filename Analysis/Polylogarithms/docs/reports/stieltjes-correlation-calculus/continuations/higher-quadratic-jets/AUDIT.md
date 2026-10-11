# Audit and claim boundaries

## Mathematical claims proved in this article

The all-order local/nonlocal decomposition, harmonic/Stieltjes compiler,
universal higher-order rigidity, resonance finite-part conversion, logarithmic
Gamma/dilogarithm primitive, all negative-integer second spectral jets,
Gamma-normalized mass transport, and polynomial-weighted two-mass second jet
and collision formulas have ordinary analytic proofs in the article.

The finite checks independently exercise implementations. They do not extend
proof status merely by succeeding. Numerical results are floating-point
diagnostics, not interval certificates. There is no formal proof-assistant
artifact and no claim of external peer review.

## What remains unresolved

The added polylogarithmic integral coordinate is sufficient but not proved
necessary. Finite Fourier reduction for third and higher negative-integer
spectral jets is not supplied. The general many-mass higher-jet interaction
problem and transcendental period-independence questions remain separate.
The Gaussian S6 and revised S8 conjectures are not changed.

## Source scope

The GitHub canonical README, source-directory metadata, incoming listing, and
repository tree were read. The full matching-title quadratic-spectrum TeX was
available from the user's Library; the targeted predecessor proof sections and
research agenda were inspected. See `PROVENANCE.json` for the exact hash.
All six binary incoming archive interiors were uninspected. No assertion is
made that this work is absent from every uninspected package or from all prior
literature. Classical anomaly, Bessel, Hurwitz, Gamma, and polylogarithm inputs
are attributed in the bibliography.

## Corrections and safeguards

No new error is asserted in the inspected predecessor's first-jet proof. Its
higher-jet warning is correct. This continuation proves the correction to
several *invalid extensions*: dropping the logarithmic-square higher-jet term,
dropping the colliding coefficient c[j,r+1]/2, discarding finite heads at higher
orders, retaining an unsubtracted divergent polynomial-weighted square, or
omitting the lower-jet term in raw mass differentiation.

The numerical implementation was adjusted to avoid a library overflow when
infinite-interval quadrature requests an astronomically tiny complex argument
of Li_1. The defining series gives the stable leading term in that regime;
this adjustment is documented and is not an error correction to a source theorem.

## Replay execution scope

A combined invocation exceeded the working environment's per-call execution
time cap. The three isolated suites each completed and produced the delivered
receipts (19, 24, and 20 comparisons). `--part all` runs those suites in
separate processes for an unrestricted local replay; its combined receipt
here is assembled from the three completed runs, not from a claimed completed
single invocation in the capped environment.
