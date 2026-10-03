# Sources and verification record

Prepared October 1, 2026. This record describes the sources actually consulted
and the boundary between proofs and computational evidence.

## Primary sources

1. OEIS A022629, https://oeis.org/A022629
   The retrieved page defines product (1+k*q^k), gives the weighted-distinct-
   partition interpretation, lists initial values, and attributes the logarithmic
   conjecture to Vaclav Kotesovec, May 8, 2018. It continued to label that formula
   a conjecture when retrieved for this report. Web retrieval may use cached
   content; the record is about the retrieved entry, not an editorial guarantee.

2. Boris L. Granovsky and Dudley Stark, *Developments in the Khintchine-Meinardus
   probabilistic method for asymptotic enumeration*, Electronic Journal of
   Combinatorics 22(4) (2015), P4.32, DOI 10.37236/4581.
   https://arxiv.org/abs/1311.2254
   https://arxiv.org/html/1311.2254v2
   The primary-source HTML was read, including its assumption 0<a_k<=1 and the
   distinct-size products with decreasing coefficients. The fixed positive
   powers inside our factors do not directly satisfy that assumption.

3. NIST DLMF, Section 4.13, Lambert W:
   https://dlmf.nist.gov/4.13
   Used for branch conventions and background, not as a source for the new
   coefficient calculations.

4. NIST DLMF, Section 25.12, Polylogarithms and Fermi-Dirac integrals:
   https://dlmf.nist.gov/25.12
   Background for the integral framework. The kernel moments required here
   are derived explicitly in the report.

5. Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
   University Press, 2009. Official companion site:
   https://ac.cs.princeton.edu/home/
   Standard background for saddle-point enumeration.

## ProveIt inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

The GitHub connector was used to read the repository README, inspect its tree
and Combinatorics directory, search for A022629, search for Lambert/transseries
material, and read:

    Analysis/Transseries/docs/series-and-transseries/
    Transseries_And_Inversion/README.md

The tree response reported commit

    dc1a7242d2ab4a4496b7dfee63256ee767b21fc9

Subsequent documentation reads used the default branch, and search excerpts
can represent another indexed commit. This identifier does not certify a
single uniform snapshot for every source consulted.

The targeted A022629 code search returned no match. This is not a complete
full-text audit of every repository artifact. The methodological connection is
the repository's treatment of polynomial-logarithmic expansions, Lambert-core
inversion, error transport, and integer-threshold inversion. The report proves
its analytic estimates independently and does not assume repository results
are automatically applicable.

## Mathematical and computational checks

- The posted leading conjecture has an elementary proof independent of the
  local limit theorem and all-orders coefficient algebra.
- The all-orders proof uses finite Taylor expansions with controlled remainders;
  it does not assume convergence of a formal infinite expansion.
- The exact-saddle proof includes a consecutive-block characteristic-function
  bound, so the central Gaussian calculation is not the only input.
- The mean expansion is derived separately, avoiding differentiation of an
  unspecified error term.
- The inverse argument transports remainders and then brackets the discrete
  threshold; it does not simply round an uncontrolled approximation.
- The largest-part limit includes a conditioning argument via a shifted local
  limit estimate. Distributional convergence is not used to infer moments.
- Exact product coefficients were computed through n=6400; the independent
  logarithmic-derivative recurrence was checked through n=100.
- Six forward and inverse coefficients were generated and checked by exact
  SymPy arithmetic in A=pi^2/(6s^2).
- Saddle diagnostics were run at n=100,400,1600,6400 using 45 decimal digits.
  The corresponding fourth-moment tail bounds are below 2e-43. They bound
  truncation, not floating-point rounding.
- The computational environment used Python 3.13.5, SymPy 1.14.0, and
  mpmath 1.3.0. See requirements.txt and the executable programs.

## Limits of the claims

The literature checks identify relevant prior work but do not certify worldwide
priority. No Lean or Rocq/Coq verification of the new theorems was performed.
The article is a research manuscript supplied for independent review.
Neither OEIS nor the user's repository was changed.

## Final artifact checks

The final LaTeX source was compiled to a 20-page A4 PDF with no unresolved
references or overfull boxes in the final build log. All pages were reviewed
in rendered contact sheets; the title, principal theorem, inverse formula,
and numerical table were also inspected at larger scale.

The delivered scripts passed Python compilation. After the final input-
validation edits, the six forward and inverse symbolic identities were rerun,
and the n=100 corrected-saddle diagnostic was reproduced at 30 digits.
An additional s=2, n=400 exact-coefficient comparison gave corrected relative
error approximately -1.9294310923e-4. The stored main data remain the original
s=1, 45-digit run. CSV row counts, indices, and diagnostic logarithms were
checked for internal consistency.
