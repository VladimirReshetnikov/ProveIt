# Source provenance and comparison boundaries

Consulted on 30 September 2026. The article contains the full bibliography.
No repository modification or new Lean build was performed.

## Repository

**Inspected fixed source**

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Path: `Algebra/SurrealNumbers/Surreal/Algebra/Geometry.lean`
- Commit: `5e0f4e05046bacda3c6ba2643f19b91aa632436b`
- Blob: `450fd4bbfc017e0da24c28e538af1cc02037ad5a`
- The first 100 source lines were read. They establish the scope as
  field-generic coordinate geometry, with dot/cross products and Gram and
  Ptolemy-related identities. The present lifting results are not asserted
  to be already formalized there.

**Context guides**

- `Algebra/SurrealNumbers/README.md`, first 220 lines read;
  fetched blob `cf63fc5ff9ca9d8877e90f8e69ec34e6ded19d23`.
- `Algebra/SurrealNumbers/docs/README.md`, its report guide and research-status
  distinctions were consulted.
- Targeted repository searches for polytope, finite geometry, and
  lexicographic/polyhedral content were used. This was not an exhaustive
  audit of all manuscripts or every repository theorem.

The repository changed during consultation; these identifiers record the
specific inspected source rather than declaring the latest repository SHA.

## Earlier companion draft

*Finite Convexity and Exact Lexicographic Optimization over the Surreals*,
research draft dated 22 September 2026, 8 pages. The user-library copy was
`article(20260923-000126).pdf`.

The title/abstract and the relevant statements were retrieved; printed
pages 5-6 were read and visually inspected. Proposition 7.1 is corrected by
a disconnected validity-set example. Theorem 9.1 is clarified by
separating optimization over the literal real domain from optimization over
its scalar extension. This draft is not an unproved dependency of the new
article. No public repository location for this copy is inferred.

## Primary mathematical sources

- Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986),
  Chapter 5: https://doi.org/10.1017/CBO9780511629143
- De Loera, Rambau, Santos, *Triangulations* (2010):
  https://doi.org/10.1007/978-3-642-12971-1
- Joswig and Smith, *Convergent Hahn Series and Tropical Geometry of Higher
  Rank*: https://arxiv.org/abs/1809.01457
  and https://doi.org/10.1112/jlms.12716
- Chirivì, Costa Cesari, Fang, Littelmann, *Higher rank
  Gelfand-Kapranov-Zelevinsky fans*, **v2, 13 September 2026**:
  https://arxiv.org/html/2604.20250v2
- Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry* (2003):
  https://doi.org/10.1007/978-3-662-05355-3
- Basu and Roy, *Quantitative Curve Selection Lemma*, v3 (2021):
  https://arxiv.org/abs/1803.00505v3
- Petrović, *On the universal Gröbner bases of varieties of minimal degree*:
  https://arxiv.org/abs/0711.2714

The recent GKZ paper's higher-rank framework is an explicit overlap, not
something claimed as a new invention here. The Graver argument is supplied
in full rather than outsourced to a reference. General real realizability
and curve selection are attributed classical tools. No literature-wide
priority certification has been made.
