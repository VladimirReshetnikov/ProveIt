# Source audit and provenance

Research date: 10 October 2026. All repository operations were reads.

## Repository observations

Repository: `VladimirReshetnikov/ProveIt`.

The last observed `main` head was
`16c7e342d7a4a15f59911f322eb90b7f96c2a8b5`, with commit timestamp
2026-10-10T22:22:13Z. This is a recorded branch observation, not a claim
that every earlier read or every incoming package was audited at that
commit. The branch was changing during the research.

The following were inspected through the GitHub connector:

* `Analysis/Polylogarithms/docs/manuscript/README.md`, observed blob
  `02774c39a68fff3792105aed3e2df11e3e604484`. This supplied scope and the
  reported distinction between proved S4 and conjectural S6/revised S8.
* The canonical manuscript directory, chapter listing, and entry-point
  `polylogarithms.tex`, for organization and integration context.
* `chapters/07-integration.tex`, particularly the Hurwitz-zeta derivative
  and negative-polygamma framework and the existing cautious treatment of
  rational reductions. The inspected text already contains the
  denominator-five log-Gamma correction; that correction is not claimed
  as a discovery of this article.
* The `docs/incoming` directory listing. The observed Gauss–Hurwitz ZIP
  had name `ProveIt_Gauss_Hurwitz_2026-10-10.zip`, blob
  `069b39cdc5a241c3e016f1780fd481dd3069d63a`, and listed size 450,539 bytes.
  Other listed archives concerned Mellin dilation, nested harmonic jets,
  polylogarithm/Stieltjes continuation, and Stieltjes/harmonic identities.

No binary incoming ZIP was unpacked from the GitHub response. Direct
container networking was unavailable, and the connector's general fetch
returns UTF-8 content rather than downloaded binary files. The corresponding
Gauss–Hurwitz article was instead read in the user's Library as described
below. Consequently, **the Library PDF was not byte-compared to the PDF
inside the repository ZIP**, and an exhaustive audit of all incoming
archives is not claimed.

## Prior article actually read

Library title: `ProveIt_Gauss_Hurwitz_2026-10-10.pdf`.

Printed title: *Gauss–Hurwitz Pole Cancellation: Resonant gamma-ratio sums,
harmonic identities, Stieltjes jets, and polylogarithmic endpoint subtraction*.
Date: 10 October 2026. Length: 23 pages.

The abstract and relevant scope/continuation passages were retrieved. Pages
19 and 20 were read with their page images; bibliography pages 22 and 23
were also read. Section 9, question 1, printed page 19 proposes a fixed
Dougall-type summation with one excess parameter and an explicit residue
polynomial. That specific target, not the entire classification question,
is addressed here. The prior article itself already warns that zero
reciprocal-Gamma values are not zero jets; the present revived-head example
is a new application of that guard, not a claim to correct that article.

Other recent Library search results showed nested harmonic and bilinear
Stieltjes continuations. These were used to avoid choosing those already
covered themes. They were not exhaustively audited or used as unproved
inputs to the present theorems.

## Classical primary sources consulted

* NIST DLMF 16.4.9: Rogers–Dougall 5F4 summation and convergence condition.
* NIST DLMF 5.11: shifted Gamma expansions and digamma asymptotics.
* NIST DLMF 25.11: Hurwitz recurrence, spectral/parameter derivatives,
  Bernoulli special values, and Gamma/polygamma connections.
* NIST DLMF 25.14: Lerch's transcendent.
* W. Chu and A. M. Fu, *Dougall–Dixon formula and harmonic number
  identities*, Ramanujan Journal 18 (2009), 11–31,
  DOI 10.1007/s11139-007-9044-6. Publisher page consulted for the direct
  harmonic-identity antecedent.
* M. Nicholson, arXiv:1801.02428v3. Its first PDF page was inspected,
  including the explicit description of the established harmonic-number
  differentiation/transformation method.
* W. Bühring, arXiv:math/0311126, published in Proc. Amer. Math. Soc.
  132 (2004), 407–415. Primary abstract and bibliographic record consulted.
* O. R. Espinosa and V. H. Moll, arXiv:math/0107082, published in
  Ramanujan Journal 6 (2002), 449–468. Primary abstract and bibliographic
  record consulted for indefinite integration and negative polygamma.

The article's bibliography contains portable source addresses. This was a
focused antecedent search, not an exhaustive priority search. Classical
methods and individual previously known specializations are not claimed
as globally new.

## Audit conclusion

No additional specific mathematical error in the inspected existing
statements was established. Four guards are documented for extending the
Gauss setup to this centered Dougall family: doubled excess, centering
before dropping odd powers, preservation of zero jets, and distinction
between finite asymptotic diagnostics and certified error bounds.

No commit, branch, pull request, or remote file was created or modified.
The integration section is an additive local proposal for review.
