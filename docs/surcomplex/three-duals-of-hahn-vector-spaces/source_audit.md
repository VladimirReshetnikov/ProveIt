# Source and proof-status audit

Audit date: September 22, 2026.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Revision: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`.

The review read the root README, the report inventory `docs/README.md`,
the introductory sections of the differential-equations and
analytic-geometry reports, and the construction, automatic-adjoint,
range-defect, and spectral sections of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`.
The recursive tree and the relevant directory listings were also inspected.

This was a targeted review of the closest material, not an exhaustive
review of every source line, archive, or historical revision. A code
search returned incomplete results and was not treated as proof that a
word or theorem was absent. No full local repository clone was available.

## Closest existing repository results

The infinite-dimensional spectral report already constructs the
coefficient Hahn--Hilbert space and its positive convolution inner
product. Its automatic-adjoint theorem identifies all everywhere-defined
adjointable operators with Hahn series of ordinary bounded operators.
It also studies range defects and spectral enlargement.

The present manuscript does not claim those results. Its strong-Hom
classification instead allows arbitrary algebraic coefficient maps, uses
a support argument rather than an ordinary closed-graph/Baire argument,
and is paired with an exact description of the completion and the much
larger continuous dual. The cofinal/noncofinal completion-intersection
formula concerns a different question from persistence of an operator's
range defect under scalar extension.

## Primary literature consulted

1. V. Bagayoko, L. S. Krapp, S. Kuhlmann, D. Panazzolo, and M. Serra,
   *Automorphisms and derivations on algebras endowed with formal infinite
   sums*, arXiv:2403.05827v2, September 22, 2025.
   https://arxiv.org/abs/2403.05827v2
   Full primary text consulted, particularly the summability and strong-map
   framework. Those notions are established, not invented here.

2. E. Kaplan, L. S. Krapp, and M. Serra,
   *Decomposing the automorphism group of the surreal numbers*,
   arXiv:2509.22374v3.
   https://arxiv.org/abs/2509.22374v3
   Primary text consulted for normal-form conventions and comparison with
   established strong-linearity terminology.

3. M. Morillon, *Multiple Choices imply the Ingleton and Krein--Milman
   axioms*, arXiv:1901.04021, 2019.
   https://arxiv.org/abs/1901.04021
   Primary PDF consulted for the non-Archimedean extension mechanism and
   its choice context. The article gives the full extension argument it
   needs rather than importing an unverified arbitrary-rank formulation.

4. A. W. Ingleton, *The Hahn--Banach theorem for non-Archimedean valued
   fields*, Proceedings of the Cambridge Philosophical Society 48 (1952),
   41--45.
   Bibliographic details and the one-step extension statement were
   corroborated in Morillon's references and discussion. The original
   full text was not obtained. The Hahn--Banach mechanism is explicitly
   treated as classical.

5. J. Aguayo and M. Nova, *Non-Archimedean Hilbert like spaces*, Bulletin of
   the Belgian Mathematical Society--Simon Stevin 14 (2007), no. 5,
   787--797.
   https://doi.org/10.36045/bbms/1197908895
   Publication metadata and abstract were accessible; the complete
   publisher PDF was not. This is a predecessor for general failures of
   familiar Hilbert-space orthogonality properties, not evidence that the
   precise coefficient-space classification in this article is known or
   unknown.

6. B. H. Neumann, *On ordered division rings*, Transactions of the American
   Mathematical Society 66 (1949), 202--252.
   Cited for classical ordered-series support facts, with the specific
   two-support lemma also proved in the article. The original paper was
   not independently audited in full during this work.

Inaccessible pages, irrelevant search results, and empty keyword searches
were not counted as evidence of bibliographic absence.

## Proposed contribution and limits

The candidate original results are the exact coefficient-rank completion
criterion and cofinality trichotomy, the strong-Hom classification in this
K-linear coefficient-space setting, the exact continuous restriction
sequence and separation of its invisible kernel, the resulting
three-dual classification, and the cofinal/noncofinal scalar-enlargement
formula. These are presented as a connected theorem package with proofs,
not as a priority-certified list of discoveries.

No named published open conjecture is claimed solved. General phenomena
such as failure of Riesz representation or orthogonal decomposition over
non-Archimedean fields are not claimed as first discoveries.

## Verification boundary

- Every stated principal theorem has a written proof in `article.tex`.
- The proofs received internal checks of hypotheses, exceptional groups,
  support finiteness, coefficient dimension, and scalar-size restrictions.
- `verify_examples.py` passed 610 exact rational assertions. These check
  finite identities and finite prefixes only.
- No Lean or other formal proof-assistant verification was performed.
- No independent refereeing or exhaustive literature/priority audit is
  claimed.

See the report JSON for the explicit list of mathematical statements the
finite program does not establish.
