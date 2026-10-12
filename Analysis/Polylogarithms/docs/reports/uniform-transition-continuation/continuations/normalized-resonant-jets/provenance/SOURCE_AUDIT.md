# Source audit and originality boundary

## Targeted repository inspection

The GitHub connector was used to read the two area overviews, the Polylogarithms manuscript overview, part of the original polylogarithm–polygamma bridge article, and the Transseries series-group, canonical-volume, confluent-critical, and q-transition overviews. `PROVENANCE.json` records known per-file blob identifiers and the inspected ranges. This is not an exhaustive review of either large corpus.

The repository already has exact-core analytic charts, Bell and Catalan coefficient mechanisms, finite Fourier polylogarithm bridges, and a detailed distinction between accepted proofs and pending claims. The present article does not claim those general techniques as new. Its overlap discussion is based on the material actually inspected, not a claim of total repository nonduplication.

The main branch moved while the work was in progress; no false common-commit snapshot is asserted. Known file identifiers are preferable to a single moving branch timestamp.

## Primary external sources

- DLMF 25.14: the exact Lerch expansion and integer-order collision, in particular 25.14.3_1 and 25.14.3_2.
- DLMF 25.11: Hurwitz zeta identities, negative-integer values, and Fourier bounds.
- DLMF 1.10(vii): coefficient-form Lagrange inversion.
- DLMF 4.13 and Corless et al. (1996): Lambert W and its branch conventions.
- Bailey–Borwein–Crandall (2014), author-hosted `MTW1.pdf`, 29 pages: raw polylogarithm order derivatives already exist in this source. Pages 12–13 were read in rendered images; the sign inconsistency is version-specific.
- Edgar, arXiv:0801.4877: general transseries background.
- Costin–Garoufalidis, arXiv:math/0701743: prior global fractional-polylogarithm continuation and monodromy. The present local result is not presented as a new general resurgence theorem.

The full URLs and bibliographic information are in the article. No external full PDF is redistributed.

## Search scope

Searches included combinations of polylogarithm, order derivative, Gamma normalization, logarithmic inversion, transseries, half-shift Hurwitz zeta, dilation filtering, and analytic cancellation curves. The literature scan located classical raw-order expansions and broad inversion/resurgence antecedents. A later focused search used these literal queries:

```text
"polylogarithm" "Gamma" "normalization" "inversion"
"Hurwitz" "half" "order" "analytic remainder"
"polylogarithm" "order" "cancellation curve"
"polylogarithm" "dilation" "logarithmic"
```

That limited scan did not establish a matching published statement of the exact half-shift tuning curve. It also did not establish worldwide novelty. Search-result absence is not used as evidence of a mathematical nonexistence or an arithmetic independence claim. The proposed originality lies in the explicit normal-form/filter/inverse construction and its arithmetic tuning refinements, subject to further bibliographic and independent proof review.

## Scope of numerical independence

The base suite compares the finite Lagrange formula with a separately coded coefficient-by-coefficient solution of the implicit equation. Direct exponential sums, direct polylogarithms, Hurwitz-tail expansions, and beta-kernel quadrature provide different numerical routes. They share mpmath arithmetic and are not independent proof-assistant or interval certificates. The all-order claims depend on the written proofs.

## Authorship and disposition

Prepared with OpenAI ChatGPT in response to Vladimir Reshetnikov's research request. The package is a proposed research contribution, not an assertion of acceptance by ProveIt Contributors. No repository files, branches, issues, or pull requests were changed.
