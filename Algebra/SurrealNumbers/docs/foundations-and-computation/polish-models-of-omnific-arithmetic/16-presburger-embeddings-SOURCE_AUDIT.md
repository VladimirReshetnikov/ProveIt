# Source and overlap audit

## Research target

The chosen topic is the structure of elementary embeddings and inherited-Polish
elementary submodels of lexicographic rational-product Presburger models.

Glazer's primary mathematical source is:

- Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1 (2023),
  https://arxiv.org/pdf/2311.13699v1.
- Its Question 2, page 8, concerns continuous addition in an uncountable Polish
  Presburger model. Its separate Question 1 concerns the metatheory of the
  topological Tennenbaum theorem. This article does not resolve Question 1.

The supplied LinkedIn profile was not accessible through public retrieval.
The research identification is grounded in the author's primary papers and the
official Epoch AI author biography at
https://epoch.ai/latest/frontiermath-competition-setting-benchmarks-for-ai-evaluation.

## Fixed ProveIt snapshot

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: `0f084afa9be466593ffa6aff37749e78c0adc733`
- Commit timestamp: 2026-10-03T19:50:54-07:00.
- Source inspection used the fixed Git objects; no repository files were changed.

The maintained source is:

`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/article.tex`

This existing manuscript already proves the affirmative examples based on
`R lex Z` and `Q^omega lex Z`. It classifies the real-coordinate model's
endomorphisms and elementary submodels and gives the initial-zero shift of the
rational-sequence model. Its further-research questions include:

1. Research question 5, **Classifying admissible coefficient groups**, asking
   about continuous order-preserving endomorphisms under suitable hypotheses.
2. Research question 8, **Polish elementary-submodel lattices**, asking which
   closed/clopen elementary-submodel lattices and intermediate behaviors occur.

The new article answers these structural questions for the specified family,
not for every possible Polish Presburger presentation.

## Existing incoming reports inspected for overlap

| Archive | Relevant existing content |
|---|---|
| `docs/incoming/polish_presburger_article.zip` | Member `polish_presburger/polish_presburger.tex`, theorem `thm:ordinals`, already constructs `M_alpha` for countable ordinals alpha >= omega. It also gives the continuous polynomial-semiring example `Z+tR[t]` and its failure of open induction. |
| `docs/incoming/polish_presburger_research.zip` | Earlier Polish Presburger constructions and associated topology. |
| `docs/incoming/glazer_proveit_local_compactness.zip` | Local-compactness obstruction for discretely ordered rings and a pointed locally compact Presburger-group classification. |
| `docs/incoming/Glazer_ProveIt_Arithmetic_Research.zip` | Standard-cut and integer-retraction arguments in bounded arithmetic; bounded truth compilation. |
| `docs/incoming/Polish_Hahn_Puiseux_Levi_Civita_Research.zip` | Polish topology boundaries for Hahn/Puiseux/Levi-Civita constructions and integer parts. |

The family `M_alpha`, its Baire-space carriers, and distinction by ordinal
Archimedean ranks are treated as prior constructions. The exact embedding
classification, ordered closed-subspace normal form, orbit/lattice consequences,
and combination of the two threshold theorems were not found in this inspected
material. This is a bounded audit, not an exhaustive search of every repository
file or every mathematical publication.

## Closest established literature

- Salma Kuhlmann and Michele Serra, *Automorphisms of valued Hahn groups*,
  arXiv:2302.06290v4, https://arxiv.org/html/2302.06290v4.
  The valuation/skeleton framework and matrix methods are established antecedents.
  The matrix section's Hahn-sum scope must be distinguished from full products.
- Michele Serra, *Automorphism groups of Hahn groups and Hahn fields*,
  Konstanz doctoral dissertation (2021), https://d-nb.info/124743740X/34.
  Strong-additivity results at discrete rank and higher-rank failures predate this
  article. The omega-stage automorphism behavior is not presented as a new
  general Hahn-group discovery.
- Pietro Freni, *On Vector Spaces with Formal Infinite Sums*,
  Applied Categorical Structures 34, 15 (2026),
  https://doi.org/10.1007/s10485-025-09844-w,
  https://arxiv.org/html/2303.08000v5.
  Provides background on formal sums, discrete-field products, and duality.
- Ilaria Castellano and Anna Giordano Bruno, *Algebraic entropy in locally
  linearly compact vector spaces*, https://arxiv.org/pdf/1612.01899.
  Section 2 recalls classical linearly compact duality. The unordered
  product-subspace mechanism is background, not a novelty claim.
- Christoph Haase, *A survival guide to Presburger arithmetic*,
  https://doi.org/10.1145/3242953.3242964.
  Classical Presburger quantifier elimination is an explicit dependency and is
  supplied in the article's appendix in the required general Z-group form.
- Alexander S. Kechris, *Classical Descriptive Set Theory* (1995),
  https://doi.org/10.1007/978-1-4612-4190-4.
  Standard Polish-space and category facts.
- Harry Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986),
  https://doi.org/10.1017/CBO9780511629143.
  Standard surreal normal-form background.

## Boundaries

- No unseen or unchecked theorem in recent AI-assisted set-theoretic preprints
  is used in the proof chain.
- No solution of an unrelated published open problem is claimed.
- No proof-assistant verification of the new results is claimed.
- The novelty assessment is relative to the sources inspected. Historical
  priority and publication-level significance remain unestablished.
