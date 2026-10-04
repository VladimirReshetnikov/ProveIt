# Source and claim audit

## Provenance and research status

This article was prepared in response to a request to connect Elliot Glazer's
research interests with Vladimir Reshetnikov's ProveIt repository and develop
new mathematics. It is AI-assisted and has not been independently refereed.
Its conclusions are accompanied by human-readable proofs, not by Lean files.
The requested deliverables are the LaTeX source and compiled PDF, provided
with reproducibility assets in this package.

The article does not claim to solve a named published Glazer problem or to
be the first proof of analytic universality for countable real closed fields.
It poses and answers local refinement questions. The exact priority of this
combined localization/threshold/genericity package remains unverified.

## Primary sources used

1. Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699.
   https://arxiv.org/abs/2311.13699
   Role: evidence of research interest in definability, topology, and models
   of arithmetic. Our parameter spaces are not domains of uncountable
   topological arithmetic models.
2. Elliot Glazer et al., *FrontierMath: A Benchmark for Evaluating Advanced
   Mathematical Reasoning in AI*, arXiv:2411.04872.
   https://arxiv.org/abs/2411.04872
   Role: research-interest connection. No current model-performance statistic
   or current employment claim is inferred.
3. F. Calderoni, D. Marker, L. Motto Ros, A. Shani, *Anti-classification results
   for groups acting freely on the line*, arXiv:2010.08049v2.
   https://arxiv.org/abs/2010.08049
   Inspected Section 7 and the displayed proofs on PDF pages 34–35.
   The broad real-closed-field embeddability result is explicitly prior work.
   Hion's lemma and colored-order completeness are attributed in the article.
4. R. Rast and D. S. Sahota, *The Borel complexity of isomorphism for o-minimal
   theories*, arXiv:1408.5876; JSL 82(2), 453–473 (2017).
   https://arxiv.org/abs/1408.5876
   Role: prior o-minimal isomorphism complexity and the countable-order route.
5. B. D. Miller, *An introduction to classical descriptive set theory*,
   Proposition 1.4.28.
   https://glimmeffros.github.io/seminars/descriptive.pdf
   Role: completeness of ill-founded trees. Our Kleene–Brouwer and
   integer-sum transformations are proved in the article.
6. L. van den Dries and P. Ehrlich, *Fields of surreal numbers and
   exponentiation*, Fundamenta Mathematicae 167(2), 173–188 (2001).
   https://doi.org/10.4064/fm167-2-3
   Together with Gonshor's monograph, this supplies standard surreal context.

Other standard references are identified in the article bibliography.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 7c0f2d9f92c3d51ec85703bed1022924a4b7359b
Accessed through the connected GitHub tools; read-only, no modifications.

Inspected material includes the root README, relevant sections of
`Algebra/SurrealNumbers/README.md`, the self-embedding report's README, and
search-returned declaration excerpts for:

* `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceRealClosed.lean`
  (the `signSequenceIsRealClosed` declaration);
* `Algebra/SurrealNumbers/Surreal/HahnSeries/RealClosed.lean`;
* `Algebra/SurrealNumbers/SurrealAudit.lean`.

Source inspection and repository documentation are not a substitute for
building or auditing the entire repository. No new result is claimed
machine-checked because a related file exists there. No unexamined assertion
from an unrelated part of the repository is used as a mathematical premise.

## External theorem boundary

The proofs use these classical mathematical inputs:

* surreal ordered-field arithmetic, real closedness, and Conway normal forms;
* algebraic extensions, real-closure uniqueness, and RCF quantifier elimination;
* Cantor's countable dense-order theorem;
* completeness of ill-founded trees;
* Borel completeness of countable linear-order isomorphism;
* Louveau's complete-analytic colored-order embeddability theorem.

The article gives its own detailed proofs of the finite-support lemma,
valuation and component calculations, quadratic-color antichain,
fixed-ambient coding, both tree transformations, finite-source threshold,
zero-one laws, and the exact complete-column criterion.

## Deliberately excluded claims

* No universal field containing every countable real closed field is claimed.
  The ambient field has the fixed residue field of real algebraic numbers.
* No order-preserving or elementary field embedding is assumed in advance to
  preserve the displayed generators; the necessary conditions use intrinsic
  natural valuations and their ordered components.
* No closure under the surreal exponential or a derivation is claimed.
* No topology, measure, or set of all subsets is placed on the proper class No.
* No explicit optimal birthday cutoff is claimed.
* No effective algorithm follows merely from an open or Borel locus.
* No total Borel witness solver exists for the stated analytic-complete locus;
  this is not a claim that arbitrary non-Borel choice is impossible.
* Analytic-completeness of a set and completeness of an analytic quasiorder
  are kept separate. Uncolored order embeddability alone does not establish
  quasiorder universality.
* Generic collapse is asserted for the rank-one family, not the entire
  coefficient-rich universal family.

## Reproducibility and validation

The Python standard-library checks use exact fractions and integers. The
recorded run passed 25,378 checks. They are finite implementation checks,
not a proof assistant verification of the infinite statements.

The PDF was compiled with pdfLaTeX in repeated passes, cross-references were
resolved, and rasterized pages were visually inspected. The final build has
no undefined citations/references and no overfull boxes. Files in the ZIP
exclude compiler intermediates and all font files.
