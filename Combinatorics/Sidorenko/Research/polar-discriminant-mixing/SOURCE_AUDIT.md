# Source audit and provenance

Prepared 7 October 2026. This audit records the sources actually used for
the final crosswalk. Exploratory repository browsing was broader than
these files, but was not a line-by-line audit of either repository.

## Pinned repositories

| Repository | Commit used for the final crosswalk |
|---|---|
| `openai/math` | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` |
| `VladimirReshetnikov/ProveIt` | `a41aa448d67395387593f1931cda142836afccdc` |

### Direct mathematical source

Repository: `openai/math`.

Path:
`preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/sections/transverse.tex`

Blob: `d4991976e630f117c8d85a7e22deb60643a2450d`.

Pinned source:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/sections/transverse.tex

The source section is **Transverse configurations and determinant signs**.
The final source reads covered its symmetric-form counts and normalization,
split-form generator count, restriction concentration proof, complementary
image identity, and local triple/pair center parametrization and probability
law (source ranges 1–155 and 175–450, with the earlier section review covering
the adjoining material).

| Source interface | Actual source statement / role | Article contribution |
|---|---|---|
| `lem:transverse-restrictions` | For an arbitrary nonempty family, `E abs(f_xi - 1/2) = O(q^(-1/2) + size^(-1/2))`; preserves this order under specified nonsingularity conditioning | Exact overlap kernel; sharp polar and Grassmannian averaging for the specific structured families |
| `eq:transverse-isotropic-count` | `N_r = 2 product_{j=1}^{r-1}(q^j+1)`, including both families | Classical count rederived; the two-family difference studied separately |
| `lem:transverse-projection` | Half-rank complementary-image projection and determinant-sign relation | Reproved in the local application |
| `lem:local-transverse` / `eq:transverse-local-l1` | Local transverse error `O(q^(-1/2))`, for `r>1` | Error `O(q^(-1))` for `r>=3`; pair case already for `r>=2` |
| `eq:transverse-three-normalization` | Triple factor `(16+O(1/q))` times the restriction-sign fraction; conditional inverse-pair law | Same exact parametrization with a sharper proved restriction estimate |
| `eq:transverse-two-normalization` | Pair factor `(4+O(1/q))` times the Grassmannian sign fraction | Same interface with sharp Grassmannian averaging |

The matching indicator remains inside the nonnegative error expectation.
The article does not condition on matching signs without controlling that
conditioning. The source's `b(n)` is the article's `c(n)=n(n+1)/2`.
The source works with fixed dimension and odd primes; the independent
finite-field results in this article hold for odd prime powers.

The manuscript title is quoted as an artifact title, not as certification
of a global Sidorenko counterexample. No audit of the entire rank-layer,
tail, global construction, or other preprints is claimed.

### ProveIt research context

Path prefix:
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/`

| File | Blob | Reviewed role |
|---|---|---|
| `README.md` | `02f1eb26decc04804b38d00bee586568701ff88e` | Research inventory: sharp local estimates, moment interpolation, restriction, collision-sensitive counting, and separation of research from formal status |
| `33-arrangement-stability-SOURCE_AUDIT.md` | `9ed4c250339f2f6172ff0765adcc3e34e24b699b` | Source-pinned local-theorem methodology, Gowers arrangement context, proof/test/priority boundaries |

Pinned directory:
https://github.com/VladimirReshetnikov/ProveIt/tree/a41aa448d67395387593f1931cda142836afccdc/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements

The inventory and audit were inspected as context. No assertion is made
that every integrated or pending ProveIt manuscript was searched completely
for duplicates, and no unverified theorem from these documents is used in
a proof. This contribution does not improve a global Szemeredi estimate.

## Primary literature and attribution

1. Kai-Uwe Schmidt, *Symmetric bilinear forms over finite fields with
   applications to coding theory*, Journal of Algebraic Combinatorics 42
   (2015), 635–670. arXiv:1410.7184.
   https://arxiv.org/abs/1410.7184
   The abstract and paper were inspected, including the page images with
   rank/type counts (Proposition 2.1) and the trace-pairing association
   scheme. The article explicitly treats these counts and the full-rank
   Fourier ingredients as classical specializations, not new general
   eigenvalue formulas.

2. Kai-Uwe Schmidt, *Quadratic and symmetric bilinear forms over finite
   fields and their association schemes*, Algebraic Combinatorics 3(1)
   (2020), 161–189. DOI:10.5802/alco.88.
   https://alco.centre-mersenne.org/articles/10.5802/alco.88/
   Used to situate the association-scheme background and possible
   characteristic-two extensions. No characteristic-two theorem is
   imported or asserted here.

3. Michael Kiermaier, Kai-Uwe Schmidt and Alfred Wassermann, *Designs in
   finite classical polar spaces*, Designs, Codes and Cryptography 93
   (2025), 1143–1162. DOI:10.1007/s10623-024-01491-x; published online
   17 September 2024.
   https://doi.org/10.1007/s10623-024-01491-x
   The Latin–Greek halving discussion and Lemma 14 establish the classical
   status of the equal proper-incidence families. The article does not
   claim that halving or its ordinary uniqueness as a new discovery.

## Research and verification boundaries

The proposed contribution consists of the explicit overlap/extension
calculus, sharp averaging laws, incidence/Fourier transfer in the present
setup, exact discriminant contrast laws, pointwise common-generator
identities, sparse-event and non-Gaussian consequences, the rank-two law,
pencil conditioning, and the local application. These have written proofs
in the delivered article. Some components may be equivalent to existing
association-scheme or polar-design specializations: historical priority is
not established by this scoped search.

The exact computational checks were performed within this preparation.
They are not a report by an independent human referee or another institution.
There is no Lean artifact and no claim of proof-assistant verification.
The further questions are proposed research questions, not all asserted to
be previously published open problems.

The final PDF was compiled and its pages rendered for layout inspection.
The delivery contains no third-party article PDFs, third-party TeX sources,
font files, or repository modifications. The companion integrity manifest
covers the actual delivered files.
