# Source and provenance ledger

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit for the inspected mathematical sources:
`a795fcffa4b3ece22761d81fbed3c43be8b81795`.

The branch later moved to `5804c7aff9955e6cbc09be2a71a295a07b238bc9`,
whose parent is the pinned commit. That commit records an incoming archive
batch, not reviewed for this article. No repository mutation was performed.

Inspected group:
`Analysis/Transseries/docs/series-and-transseries/`

1. Group `README.md`: arrival descriptions and status qualifications,
   especially source lines 265–410. An earlier range read was truncated;
   the article does not claim an exhaustive read of every README line.
   Blob SHA: `f2cf02dbb23661e60ce6be751989b5b7bc8e1a46`.
2. `Exponential_Feedback_Regularity_Classification/README.md`: model,
   verification summary, and explicit limits, read in full.
   Blob SHA: `58347fd1f58f934908633ec729d8fb29ca73fa8e`.
3. `Critical_Transseries_Moving_Fold/article.tex`: source lines 1400–1580,
   including the final research questions, conclusion, and scope statements.
   Blob SHA: `72fe473ddef084acf4b8761fd0459480f4afee3f`.
4. Directory/tree listings were used to identify neighboring packages and
   avoid repeating the already-covered directions.

The full canonical transseries volume and the newly arrived archives were
not audited. No unreviewed repository result is used as a mathematical
premise in the proofs of this article.

## Primary literature and reference material

- NIST DLMF, Section 25.12, Equation 25.12.12:
  https://dlmf.nist.gov/25.12
  Used for the convergent polylogarithm expansion near t=1.
- Flajolet and Sedgewick, *Analytic Combinatorics* (2009), author book site:
  https://ac.cs.princeton.edu/
  Classical background for Lagrange inversion and singularity analysis.
- Svante Janson, *Simply generated trees, conditioned Galton–Watson trees,
  random allocations and condensation*, Probability Surveys 9 (2012),
  103–252, doi:10.1214/11-PS188.
  https://arxiv.org/abs/1112.0510
  The preprint PDF's critical infinite-variance discussion, including
  Example 18.27, was inspected. Its stable scale and allocation/maximum
  phenomena are important prior art, not claimed here as new general facts.
- Arijit Chakrabarty and Gennady Samorodnitsky, *Understanding heavy tails
  in a bounded world or, is a truncated heavy tail heavy or not?*,
  Stochastic Models 28(1) (2012), 109–143,
  doi:10.1080/15326349.2012.646551.
  https://arxiv.org/abs/1001.3218
  Conceptual precedent for soft and hard truncation regimes.

Consultation date: 29 September 2026.

## Research status

The combined Hahn/Fourier/cutoff analysis is presented as a model-specific
extension, with full proofs, not as a globally certified priority claim.
The relation to simply generated trees makes broad stable-limit novelty
claims inappropriate. The article distinguishes this established mechanism
from its explicit formulas, coefficient matching, and repository application.

The numerical program is an accompanying implementation, not a source for
the infinite theorems. It performs exact rational and symbolic checks and
separately reports floating-point diagnostics. No Lean verification,
peer review, or interval-arithmetic certification is claimed.
