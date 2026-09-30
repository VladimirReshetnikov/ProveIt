# Source and provenance manifest

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit inspected: `ebd8344bca77d8352cd745b7df374618a290a029`.
The branch endpoint was queried and the commit identifier recorded.
Read-only repository inspection; no upstream modifications were made.

Primary manuscript:

`Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex`

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/ebd8344bca77d8352cd745b7df374618a290a029/Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex

The relevant research target is Question 1, "Slowly varying action tails,"
in the section "Further research questions and concrete targets." The
model, exact coefficient/Poisson identities, and scope statements were also
inspected. Needed mathematical claims are proved in the new article rather
than assumed on the authority of an unreviewed repository manuscript.

Additional repository documents inspected:

- `Analysis/Transseries/README.md`.
- `Analysis/Transseries/docs/series-and-transseries/README.md`, including
  the indexed descriptions of recent critical-Hahn, logarithmic-endpoint,
  regularity, finite-core, and related research packages.
- Repository directory/tree metadata and `branches/main` commit metadata.

This is a targeted comparison, not a claim-by-claim audit of the entire
repository or every incoming archive. It does not establish historical
novelty or exhaustively exclude independent overlapping work.

## Primary mathematical references

1. N. H. Bingham, C. M. Goldie, J. L. Teugels, *Regular Variation*,
   Cambridge University Press, 1987.
   https://doi.org/10.1017/CBO9780511721434
   Used for uniform convergence/Potter bounds, asymptotic inversion, and
   de Bruijn conjugacy. The model-specific Abelian and Fourier estimates
   are proved in the article.

2. S. Janson, *Simply generated trees, conditioned Galton-Watson trees,
   random allocations and condensation*, Probability Surveys 9 (2012),
   103-252. https://doi.org/10.1214/11-PS188
   https://arxiv.org/abs/1112.0510
   The HTML version was consulted for the classical allocation, conditioning,
   stable-law, and maximum-component context. Published and arXiv section
   numbering differ; the new article does not rely on an ambiguous section
   number as a substitute for its own proof.

3. NIST DLMF, 25.12, especially 25.12.12, the polylogarithm expansion.
   https://dlmf.nist.gov/25.12.E12
   This exact convergent identity is parameter-differentiated for integer
   logarithmic powers.

4. NIST DLMF, 4.13, Lambert W function and real branches.
   https://dlmf.nist.gov/4.13
   The relevant core uses W_-1 because its logarithmic coordinate tends
   to positive infinity.

5. G. A. Edgar, *Transseries for beginners*, arXiv:0801.4877 (2008).
   https://arxiv.org/abs/0801.4877
   Background on transseries terminology and formal/analytic distinctions.

Sources accessed September 29, 2026. Bibliographic details and clickable
references are also included in the article. The literature review was
targeted, not exhaustive. No external manuscript or font file is redistributed.
