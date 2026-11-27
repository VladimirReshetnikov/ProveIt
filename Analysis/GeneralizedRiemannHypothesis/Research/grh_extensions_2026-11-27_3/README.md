# Two extensions of the ProveIt GRH transfer program

Prepared 27 November 2026. This archive contains two complete mathematical
research notes, their LaTeX sources and compiled PDFs, exact-arithmetic
verification programs, recorded outputs, a figure, and source/review evidence.

Source repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/6d284fcf75bc3a91bb2e79ba7636f94724bff62c/Analysis/GeneralizedRiemannHypothesis).
All repository comparisons are pinned to commit
`6d284fcf75bc3a91bb2e79ba7636f94724bff62c`.

## 1. Every sparse prime-product transition is compound Poisson

Read `prime_product_limits.pdf`; the editable source is
`prime_product_limits.tex`.

Retain any fixed positive fraction a of the primes up to C(log q)^2, excluding
primes dividing q. Let m be the retained population, k the chosen cardinality,
h=min(k,m-k), and D=floor(1/a). Assume h>=B log q and h/m tends to zero.

The note proves:

1. A necessary and sufficient mixing criterion at every fixed retained density:
   h/m times the least minority count of a nonprincipal character of order at
   most D must tend to infinity.
2. A complete subsequential classification on the normalized pointwise scale:
   after a deterministic phase correction and passage to a finite quotient of
   order at most D, every limit is compound Poisson. Diverging defect rates
   generate a subgroup on which the law becomes uniform.
3. A converse: every permitted finite-group compound-Poisson law is realized
   by retained prime sets, including exact reciprocal-density boundaries.
4. A group-valued finite-population expansion with an explicit signed correction
   of order 1/h and a uniform O(h^-2) remainder when ht/m is bounded. The
   comparison is with the current independent Bernoulli law; replacing this
   by a fixed Poisson limit at the correction scale is generally invalid.

The arithmetic applications use the supplied Dirichlet GRH theorem. The finite
probability lemmas are unconditional. Constants B,C are existential and are
not optimized. Neither vanishing retained density nor shorter quotas are covered.

## 2. First-digit optimality for symplectic blocks over local rings

Read `symplectic_precision.pdf`; the editable source is
`symplectic_precision.tex`.

Let a block between symplectic frames of dimensions 2a and 2b be observed in a
Haar symplectic matrix of ambient dimension 2n. Over any complete discrete
valuation ring with finite residue field F_q, if

    n >= a + b + min(a,b) - 1,

its total variation distance from independent additive-Haar entries is exactly
the same at every finite precision and over the complete ring. The optimal
equal-prior test is singularity, modulo the uniformizer, of the residual
alternating form J_b + M^T J_a^{-1} M.

The note gives the exact distance, an O(ab) residue-field computation inherited
from the source, a proof valid in residue characteristic two, and an exact
Fourier algorithm for higher local densities. It also proves that the Gram law
C^T J_c C on alternating s-by-s matrices (s>=2) has a bounded density exactly
when c>=s-1, with a continuous density in that range and sharp uniform precision
decay exponent 2c-2s+3.

These results are unconditional. The testing range is sufficient; it is not
claimed to be optimal. Equal-prior optimality does not imply that higher digits
are irrelevant for every prior, loss function, or repeated-observation problem.

For q=2,a=b=2,n=5, the exact all-precision total variation distance is

    197449 / 5936128 = 0.033262254452734175...

## What is new relative to the inspected collection

The source already contains the bounded-quotient reduction, quadratic/cubic
criteria, a scalar quadratic correction, exact quarter-density support
criteria, the single-pair local theorem, and a multi-pair finite-field optimal
test. The papers credit these predecessors. The proposed additions are the
complete all-density sparse limit classification and group-valued correction,
and the multi-pair all-precision local-ring theorem with Gram-density
regularity. See `evidence/source_audit.md` for the comparison.

These are complete written proofs with independent internal mathematical
reviews and exact finite checks. They have not been formalized in Lean,
externally peer reviewed, or certified as historically first. The upstream GRH
formalization was not rebuilt as part of this work.

## Reproduce the verification

From this directory, with Python 3.10 or later:

```sh
python3 -m pip install -r requirements.txt
python3 code/verify_prime_products.py
python3 code/symplectic_precision_verify.py
```

The symplectic verifier uses only the Python standard library. The prime-product
identities also use standard-library exact rational arithmetic; NumPy and
Matplotlib generate the illustration. The included run used Python 3.12.14,
NumPy 2.3.5, and Matplotlib 3.10.8. JSON decimal displays and plotted values are
approximations; finite identity assertions use exact arithmetic.

The recorded checks include:

| Check | Count |
|---|---:|
| Prime-product population/quota cases | 2,026 |
| Independently enumerated subsets | 77,166 |
| Exact factorial-ratio inequalities | 44,280 |
| Symplectic alternating residual matrices | 9,714 |
| Independently enumerated one-pair Gram inputs | 137,889 |
| Independently enumerated observed matrices | 72,097 |
| Strict local-density lower-bound parameter cases | 1,728 |
| Fourier conductor-recursion cases | 60 |

Both programs passed all assertions. Finite checks help detect mistakes in
formulas and conventions; the infinite families follow from the written proofs.

## Rebuild the PDFs

A normal TeX Live installation with pdfLaTeX, Latin Modern, AMS packages,
geometry, microtype, hyperref, xurl, booktabs, and graphicx is sufficient:

```sh
bash code/build_pdfs.sh
```

The figure PDF is already included. Regenerating it is optional. Both manuscripts
have inline bibliographies, so BibTeX is unnecessary. File hashes will naturally
change if regenerated with different tools or PDF metadata.

## Contents

| Path | Purpose |
|---|---|
| `prime_product_limits.tex`, `.pdf` | Main arithmetic research note |
| `symplectic_precision.tex`, `.pdf` | Companion local-algebra research note |
| `code/` | Two exact verifiers and the PDF build script |
| `data/` | Recorded verification and example outputs |
| `figures/` | Prime-product transition and correction figure, PDF/PNG |
| `evidence/source_audit.md` | Dependency and novelty comparison |
| `evidence/source_inventory.tsv` | Git blob hashes for 39 retrieved source files |
| `evidence/*independent_review.md` | Independent internal proof reviews |
| `evidence/build_verification.json` | Compilation and document checks |
| `requirements.txt` | Figure-generation dependencies |
| `SHA256SUMS` | Hashes of the delivered files |

The source manifest records the files checked against the pinned Git tree. It
does not imply a line-by-line audit of every theorem in the upstream project.
