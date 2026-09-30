# Source audit

Sources were consulted on 29 September 2026 (local report date). Repository
content was read using the connected GitHub tool. Public primary literature
was consulted through web retrieval. No third-party articles or font files are
redistributed in this archive.

## 1. ProveIt binary open-query baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864`

Directory:
`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/open-query-membership-games/`

Pinned report:
https://github.com/VladimirReshetnikov/ProveIt/tree/5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/open-query-membership-games

Inspected: the full README and lines 1–160 of `article.tex`, plus repository
search results and part of the report manifest. The baseline states a binary
layer/decision-tree normal form, finite Cantor–Bendixson classification, and
binary topological-sum counterexamples. This article does not claim those
results anew. The baseline's reported computations were not rerun here; the
present verifier is independent and has different, explicit coverage.

## 2. Topological games

Lucas Chiozini, Tamás Csernák, Lajos Soukup,
*Gamification of the T_0-pseudoweight via cut-and-choose games on topological spaces*.
https://arxiv.org/html/2510.05754v3

Used for the game context and the topological-sum question. The article does
not claim solutions of the source's general transfinite or point-separation
questions. The citation is version-specific; this audit does not assert that
there can be no newer version or independent subsequent solution.

## 3. Modified shortest common supersequence hardness

Aurélie Lagoutte and Sébastien Tavenas,
*The complexity of Shortest Common Supersequence for inputs with no identical
consecutive letters*.
https://arxiv.org/abs/1309.0422
https://arxiv.org/pdf/1309.0422

The retrieved PDF is marked arXiv:1309.0422v2, 8 January 2015. Its internal
front-page date differs; the article cites the arXiv version rather than
inventing a journal publication date. The definition on page 1 and Corollary 6
on page 7 establish the imported three-letter modified-SCS hardness theorem:
no equal adjacent input letters, no input word starting with a designated
letter. The source uses a strict length budget; the article explicitly shifts
it to a non-strict budget. Screenshots of the definition and corollary pages
were inspected.

The source also discusses Alain Darte's *On the complexity of loop fusion*,
Parallel Computing 26(9):1175–1193 (2000), and its typed-chain connection.
Darte's paper was not independently read in full; the article attributes that
connection through Lagoutte–Tavenas rather than claiming a direct audit.

## 4. Multi-valued descriptive context

Victor Selivanov, *Towards a Descriptive Theory of cb_0-Spaces* (2014).
https://arxiv.org/abs/1406.3942

Used only to acknowledge the established study of k-partitions and difference
hierarchies. No theorem from this paper is imported into the proofs. This is
not a complete review of that literature.

## Priority boundary

Searches for related open-query/supersequence terminology were limited and
sometimes returned irrelevant results, which were not used. Failure to find
an equivalent theorem does not establish novelty. The article supplies proofs
and a precise comparison to the inspected binary baseline, not a certified
claim of first discovery.
