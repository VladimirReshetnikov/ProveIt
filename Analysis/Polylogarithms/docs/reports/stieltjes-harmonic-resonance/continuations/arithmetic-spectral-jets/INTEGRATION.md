# Proposed ProveIt integration

## Destination

Suggested new directory:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/arithmetic-spectral-jets/`

Copy this package there as a self-contained report, reconciling the thematic spine
with `OVERVIEW.md` as required by the current Polylogarithms intake procedure. No overwrite or repository
mutation has been performed. The modular master and one-file master are
alternative representations; do not input both into one build.

## Research-status update

In `resonant-jets-and-shifts/sections/08-audit-research.tex`, Q10 can be updated
by appending the following status paragraph (not deleting the original question):

> The arithmetic-spectral-jets continuation proves the extension for
> quasi-polynomial weights and multiplicative Hurwitz lattices, including
> divisor multiplicities. A general finite-principal-part theorem handles
> several and higher poles under explicit meromorphic continuation and
> absolute-convergence hypotheses. It supplies all local finite differences,
> all individual Hurwitz-product jets, and compensated Abel untwisting.
> Arbitrary arithmetic Dirichlet series without those hypotheses remain
> outside the theorem's scope.

This is a completion of the stated concrete extension, not a claim that every
arithmetic multiplicity is meromorphically regularizable.

## Main labels

| Component | Label |
|---|---|
| Normally convergent tail | `asj:thm:tail` |
| Finite-principal-part transfer | `asj:thm:transfer` |
| Normalized Laurent-jet polynomiality | `asj:thm:polynomial` |
| Highest local polarization | `asj:thm:top` |
| All local differences | `asj:thm:all-differences` |
| Quasi-polynomial mean law | `asj:thm:mean` |
| Two-pole sigma_1 anomaly | `asj:thm:sigma` |
| All individual Hurwitz-product jets | `asj:thm:alljets` |
| Higher-pole alternant | `asj:thm:alternant` |
| Six-term divisor first jet | `asj:thm:six` |
| Centered Gamma reciprocity | `asj:thm:gamma` |
| Reciprocal polygamma formulas | `asj:thm:polygamma` |
| Anchored reciprocal primitive | `asj:thm:primitive` |
| All harmonic single-shift jets | `asj:thm:harmonic` |
| Compensated Abel untwisting | `asj:thm:untwist` |
| All-order explicit compensation | `asj:thm:bellcounter` |

Intake should not modify the unified manuscript; such changes belong in a separate
subsequent manuscript commit. In that later step, the canonical
integration/differentiation chapters could cite the
Gamma reciprocity, primitive, and harmonic identities. The main continuation
should retain the full analytic hypotheses and the fixed Laurent coordinate.
Macros in the standalone preamble should be reconciled before importing a
section into the canonical manuscript; label names are already namespaced.

## Required safeguards

1. `r![s^r]F(s)` is not an ordinary derivative at zero when F has a pole.
   In particular, the double-divisor single-shift residue is exactly `-a`.
2. Keep every principal-part coefficient, not only the highest residue.
   Coefficients through order `r+H` can contribute to an order-r jet.
3. Keep all Gamma summand subtractions grouped and the primitive anchored.
4. Do not remove the untwisting compensation or silently exchange the limits.
5. Preserve classical attribution for the simple-pole anomaly, the elementary
   Gamma/Hurwitz formulas, and the earlier polynomial/logarithmic calculus.
6. Do not change S4/S6/S8 status on the basis of this package. S4 is already
   proved; the old S8 vector is rejected; S6 and a distinct newer S8 remain
   conjectural at the inspected revision.

## Verification artifacts

The exact checks are finite algebra, not proof-assistant certificates for
analysis. The numerical files are reproducible diagnostics, not interval proofs. Run suites
on a scratch copy during intake because they rewrite result JSON files.
The compact six-term certificate is also written in ordinary mathematics in
Section 6. It can be formalized without implementing numerical polylogarithms.
