# Source and provenance notes

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected reference:
`04473354a0f3edff2d6c365caf26170ca6b88735`.

Primary predecessor:
`Analysis/Transseries/docs/series-and-transseries/Inverse_Harmonic_Stokes_Transport/inverse_harmonic_transseries.tex`.

Returned predecessor content blob:
`2da951cd1d724042f9784365a448c584984ece74`.

The focused GitHub reads covered its normalization and coefficient formula,
centered Fermi integral, explicit bracket, sharp forward-truncation inverse proof,
and research questions. The decisive labels are:

- `prob:direct`: sharp direct inverse partial sums, especially bounded `M-pi*X`.
- `thm:optimal`: forward-truncation inverse, a different approximation.
- `lem:fermi`: exact centered integral and signed remainder.

The transseries-group README and canonical-volume README were also inspected.
The group README explicitly states that the predecessor does not claim the sharp
remainder of a direct partial sum. Other new packages in that README cover q-to-1
transitions, nonlinear Stokes transport, countable feedback, and action accumulation.
The present work selects the specific direct-truncation gap instead of repeating
those projects.

The large canonical volume was not exhaustively read. No complete nonduplication
audit of every file or every new repository arrival is claimed.

A later branch read returned `db68f0853c3c69cd930caedab6f6ad9addb11eaf`, whose parent
was the inspected reference. This confirms that the repository was moving during
the work. The article pins its actual input instead of describing it as current.
The later commit concerned other research consolidation; the present article does
not rely on its contents.

## External mathematical antecedents

The bibliography records the primary sources consulted or used:

1. Issaka, *On Ramanujan's inverse digamma approximation*, Ramanujan Journal 39
   (2016), 291-302, DOI 10.1007/s11139-014-9659-3; online publication 8 January 2015.
   Its coefficient and coefficient-asymptotic subject is acknowledged as prior work.
2. Issaka's 2014 CEU master's thesis, especially its inverse-digamma chapter.
3. Gessel, *Lagrange inversion*, arXiv:1609.05988.
4. Fabijonas and Olver, *On the reversion of an asymptotic expansion and the zeros
   of the Airy functions*, SIAM Review 41 (1999), DOI 10.1137/S0036144598349538.
5. NIST DLMF Sections 5.5, 5.9, and 5.11 for classical gamma-function identities,
   integral representations, and shifted Stirling expansions.
6. Sauzin, *Nonlinear analysis with resurgent functions*, Ann. Sci. ENS 48 (2015),
   DOI 10.24033/asens.2255, arXiv:1212.4477. General resurgence closure is credited
   as existing theory and is not used as a substitute for the direct error proof.

This was a targeted search, not an exhaustive literature review. The specialized
cutoff-transfer and direct-remainder results are presented with proofs, without a
claim of established global priority.

## Verification boundary

The article contains conventional analytic proofs. Symbolic assertions verify the
printed low-order algebra. The 312-digit mpmath calculations are consistency tests,
not interval certificates. The six standard-library rational certificates verify
finite inverse-error enclosures using the analytic identities and derivative
bounds proved in the article; those identities themselves are not checked by a
proof-assistant kernel.

The result settles the bounded-offset part of `prob:direct`, including eventual
local enveloping. It leaves global enveloping, explicit universal thresholds,
growing amplitude order, and complex-sector extensions as further questions.
No Lean implementation, independent refereeing, or repository write is claimed.
