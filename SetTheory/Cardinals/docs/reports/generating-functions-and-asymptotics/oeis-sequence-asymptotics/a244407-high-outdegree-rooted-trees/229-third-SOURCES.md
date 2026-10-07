# Source scope and numerical provenance

Report 229, 5 October 2026, continues our delivered Report 227. The new article
states the model and definitions in full, then proves the exact third sector,
all-size deficit congruence, root-tail identity and remainder, first following
boundary, and both negative-even-pole cancellations. No worldwide priority
claim is made.

## Included baseline

The directory public227 contains only our unchanged Report 227 TeX and PDF.
The PDF SHA-256 is
9bb2da87d84c9aa12637c2f9d7a3c359d20315b1c62ee6dde3f4a76a3f889687.
Its public mathematical definitions and classical analytic normalization are
inherited; its code is not imported. The exact third-sector verification is
self-contained in code/.

## Classical analytic attribution

- Otter (1948), https://doi.org/10.2307/1969046: rooted-tree counting and the
  classical square-root singularity framework
- Schwenk (1977), https://doi.org/10.1016/0012-365X(77)90008-5: cycle-index
  asymptotics and the classical critical constant, as compared in Report 227
- Drmota and Gittenberger (1999), author manuscript
  https://dmg.tuwien.ac.at/bgitten/preprints/nodedeg.pdf: degree-distribution
  context and normalization; its b sqrt(rho-z) is beta sqrt(1-z/rho), with
  beta = b sqrt(rho)
- Genitrini (2016), https://arxiv.org/abs/1605.00837: full asymptotic expansions
  for Pólya structures; the arXiv record was checked again for this continuation
- Flajolet and Sedgewick (2009), https://ac.cs.princeton.edu/home/: the general
  singularity-transfer and recursive-structure framework; the author booksite
  was checked again for this continuation
- Corless et al. (1996), https://doi.org/10.1007/BF02124750: Lambert W and branch
  conventions, used only to restate the inherited leading inverse

The new article credits these methods. It does not present a new general
transfer theorem. A convergent local Puiseux expansion does not imply that the
resulting infinite coefficient asymptotic expansion converges.

Gittenberger (2006), author manuscript
https://www.dmg.tuwien.ac.at/bgitten/preprints/largedeg.pdf, is inherited source
context for growing-degree regimes. As emphasized in Report 227, an absolute
O(1) error on a mean is not a relative estimate for an exponentially small event.
The new exact type-deletion proof does not import such a relative conclusion.

## OEIS attribution

- https://oeis.org/A244372: rooted unlabeled maximum-outdegree triangle
- https://oeis.org/A244407: even diagonal T(2n,n), n >= 1
- https://oeis.org/A244410: odd diagonal T(2n+1,n), n >= 1, plus its specified
  exceptional zeroth term

The earlier leading constants recorded in A244407 and A244410 are attributed
to Vaclav Kotesovec, 11 July 2014. That attribution and the exact diagonal
identities are carried over from Report 227. This continuation did not perform
a new b-file comparison and does not relabel generated exact fixtures as OEIS
downloads. Its U,V sequences are generated directly from the proved formulas.

## Unresolved priority comparison

Goh and Schmutz, Unlabeled trees: Distribution of the maximum degree,
Random Structures & Algorithms 5 (1994), 411–440,
https://doi.org/10.1002/rsa.3240050304, still requires full-text comparison.
The DOI route was not accessible in this preparation, and the full text had
not been obtained in Report 227's comparison. Publisher records, fragments,
and later statements of a logarithmic central-window theorem cannot exclude
an overlapping rare-tail lemma elsewhere in the original. This limitation
remains explicit. No access restriction was bypassed.

## Evidence and limits

- Infinite exact identities and asymptotic claims are proved in report229.tex
- Finite coefficient, literal-tree, root-tail and symbolic checks corroborate
  algebra, conventions and implementation
- Decimal calculations use finite analytic-tail cutoff 360 and 70 working
  digits by default; neither truncation nor rounding errors are interval-bounded
- Every fixed order means a chosen finite order with its own remainder, not
  convergence, optimal truncation, or a complete exponential transseries
- Earlier-sector fixed-order remainders can exceed later entire sectors
- The -7/-6 result is one boundary only, not a full fourth sector
- No new two-parameter inverse theorem or certified rounding algorithm is claimed

External copyrighted papers and nonpublic research materials are not included.
Links are bibliographic source pointers, not a statement that every linked full
text was newly consulted during this continuation.
