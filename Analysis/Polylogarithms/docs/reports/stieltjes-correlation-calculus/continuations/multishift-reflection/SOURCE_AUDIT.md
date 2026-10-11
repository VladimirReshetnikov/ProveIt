# Source audit and research scope

## Repository anchor

Observed branch head: `f7e35be357654198c1546fd40f363694c5bcc2cc`.
Observed commit timestamp: `2026-10-11T03:35:18Z` (10 October, America/Los_Angeles).
Repository: `VladimirReshetnikov/ProveIt`.

The branch response, canonical manuscript README, chapter listing, and incoming listing were read through the GitHub connector. Selected incoming archive text was read through Wolfram's import of the public repository. Local direct network downloads failed; no claim is made that a complete checkout was available.

## Substantive reads

- `Analysis/Polylogarithms/docs/manuscript/README.md`: organization, proof status, provenance, and unresolved S6/S8 scope.
- `Analysis/Polylogarithms/docs/manuscript/chapters/04-S4-proof.tex`: substantial source excerpt, showing the already proved S4 certificate and its research boundary. S4 is not claimed anew.
- `docs/incoming/ProveIt_Continuous_Depth_Lerch_2026-10-10.zip`, member `ProveIt_Continuous_Depth_Lerch_2026-10-10/article.tex`: principal formulas, conventions, Gamma kernel, entire spectral family, centered reflection and odd values, harmonic master, and the complete further-research section. Q4 and Q8 are the explicit targets continued here.
- READMEs only of the Tilted Lerch Binary Cancellation, Mixed Resolvents Harmonic Powers, and Algebraic Gauss Centered Harmonic Reflection archives: used to avoid overlap and to credit already announced results. The report reproves the narrow anchor expansion it uses and does not assume correctness of an unread analytic proof.
- Selected repository research-question search results were reviewed as context; disconnected search snippets were not used as proofs.

The Canonical Digamma Fifth Moment and Higher Digamma Powers archives were inventoried but not substantively audited. Other repository material was not exhaustively reviewed. Archive names and passing replay statements do not establish analytic correctness.

## Primary literature

The accessible PDF text of Johansson and Blagouchine, arXiv:1804.01679v3, equation (2), explicitly states Re(a)>1/2 for the raw hyperbolic Stieltjes formula. Two web screenshot requests failed with a cache-miss error. No visual review of that external PDF is claimed. The formula and hypothesis were available in parsed text; no diagram or table was needed for the mathematics.

Chakrabarti–Srinivasan's arXiv abstract identifies the Gamma-product Fourier transform as classical. DLMF Sections 5.7, 5.12, 5.15, 25.11, 25.12, and 25.14 were consulted for conventions and elementary special-function inputs. Cheng–Hu's abstract was read for additional classical Jensen context; no theorem from its full text is used.

## Corrections versus safeguards

No false theorem was found in the inspected source portions. The report gives three explicit counterexamples to invalid extensions, not accusations against the sources: a missing branch-cut correction, a missing cubic overlap term, and a missing centered half residue. The source Johansson–Blagouchine formula is correct in its stated domain.

Additional safeguards fix pole–zero products before spectral differentiation, retain the balanced constant term, keep complex Gamma products distinct from absolute squares, and specify the common finite-part scale. Historical novelty and arithmetic independence remain unestablished.

## Source questions

Continuous-Depth Q4 asks for independent resolvent shifts in centered reflection, all spectral jets, and collision/branch rules, using old unequal-center expansions as input. The report supplies the horizontal-cut completion and its holomorphic collision law. Noninteger centered singular integrals are interpreted by the stated joint continuation, not falsely called ordinary integrals.

Continuous-Depth Q8 asks for spectral derivatives at odd integer evaluation points while retaining necessary Gamma, Stieltjes, and generalized-Z jets. The report gives exact finite Bell formulas on both odd and even lattices. It does not separately evaluate every retained generalized-Z derivative in a smaller constant space.

## Integration status

All outputs are proposals for additive integration. No repository mutation or canonical-volume rebuild was performed. The article is not peer-reviewed or formalized, and should receive independent mathematical review.
