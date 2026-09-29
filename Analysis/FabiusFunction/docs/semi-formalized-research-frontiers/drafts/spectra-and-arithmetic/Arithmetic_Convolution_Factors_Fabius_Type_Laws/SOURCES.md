# Sources and audit scope

Prepared 28 September 2026. These records distinguish verified background
and inspected repository context from the article's own mathematical proofs.

## Repository snapshot

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Inspected main-tree commit: `fbba58593dc0622aa914972896150d4848f935b5`.
- Tree metadata was obtained through the GitHub connector. No files in the
  user's repository were modified.

### Relevant documentation actually retrieved

1. Inverse and sampling README:

   https://github.com/VladimirReshetnikov/ProveIt/blob/fbba58593dc0622aa914972896150d4848f935b5/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/README.md

   The returned text described geometric-uniform moment and reciprocity
   infrastructure, probability/Laplace results, and deconvolution research.
   Its ending was truncated; no assertions here depend on unread text.

2. Shape, divisibility, and Stein geometry README:

   https://github.com/VladimirReshetnikov/ProveIt/blob/fbba58593dc0622aa914972896150d4848f935b5/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Fabius_Rvachev_Shape_Divisibility_Stein_Geometry/README.md

   This README was retrieved in full. It explicitly identifies an
   identical-convolution rootlessness strand and warns against confusing
   manuscript theorem labels with exact Lean counterparts. The article
   acknowledges that rootlessness overlap instead of claiming priority.

### Important retrieval limitation

Navigation confirmed this larger source:

https://github.com/VladimirReshetnikov/ProveIt/blob/fbba58593dc0622aa914972896150d4848f935b5/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/geometric_q_fabius_frontiers/geometric_q_fabius_frontiers.tex

The approximately 1.28 MB TeX file could not be fetched through the connector
because of its supported response-size limit. It was not fully read. Hence
this package does not certify that none of its results occurs somewhere in
that monograph or in other uninspected repository documents.

Targeted GitHub code searches were also used to locate relevant documents.
Search-term matches or nonmatches are not treated as exhaustive evidence of
novelty. The main theorems in this package are proved independently from
explicit assumptions rather than imported from unseen repository material.

## Primary mathematical sources

### Fabius

J. Fabius, "A probabilistic example of a nowhere analytic C-infinity-function,"
Zeitschrift fuer Wahrscheinlichkeitstheorie und verwandte Gebiete 5 (1966),
173–174.

CWI primary archival record: https://ir.cwi.nl/pub/8160

Used as historical context, not as the source of the new classification.

### Arias de Reyna

J. Arias de Reyna, "An infinitely differentiable function with compact support:
Definition and properties," English translation (2017) of the 1982 Spanish
article in Revista de la Real Academia de Ciencias Exactas, Fisicas y Naturales
76, 21–38.

- Record: https://arxiv.org/abs/1702.05442
- PDF: https://arxiv.org/pdf/1702.05442

The primary PDF was read and pages 2 and 3 were inspected as rendered images.
Equations (4) and (9) explicitly support the normalized dyadic sinc product
and the zero multiplicity 1+v_2(n). Those facts are attributed in the paper,
not claimed as new. The ladder extension is proved independently.

### Hutchinson

J. E. Hutchinson, "Fractals and self-similarity," Indiana University Mathematics
Journal 30 (1981), no. 5, 713–747.

- DOI: https://doi.org/10.1512/iumj.1981.30.30055
- Primary journal record: https://www.iumj.indiana.edu/docs/30055/30055.asp

Used to identify classical self-similar-measure context. All particular
existence, uniqueness, pure-type, atomlessness, and regularity arguments
needed for the present digit laws are supplied in the article.

### Harrington–Kechris–Louveau

L. A. Harrington, A. S. Kechris, and A. Louveau, "A Glimm–Effros dichotomy for
Borel equivalence relations," Journal of the American Mathematical Society
3 (1990), no. 4, 903–928.

- DOI: https://doi.org/10.1090/S0894-0347-1990-1057041-5
- Primary author-repository record:
  https://authors.library.caltech.edu/records/cvb33-qt212

Used for classical descriptive-set-theoretic context. The article does not
claim a new theorem about E_0 itself or rely on the full dichotomy theorem.
It gives a self-contained zero–one proof of the obstruction it uses and
an explicit realization by smooth convolution factors of the Rvachev law.

## Claims not made

No exhaustive literature review, settled priority claim, Lean verification,
peer review, or resolution of a separately verified named longstanding
conjecture is represented by this source audit. The ten further questions
are proposed extensions and boundaries of the present proofs; their global
open status should be independently audited before advertising them as
new open problems.
