# Sparse equations for singular moduli

Read **report.pdf** for the statements, proofs, source analysis and references. The main question is the minimum number of nonzero terms of a nonzero rational polynomial that vanishes at a given singular modulus. Its degree can be arbitrarily large.

## Results

- At most four terms are possible exactly in degrees at most three. The original incoming report left 79 quartic and quintic discriminants for this question. A parallel manuscript also settled this classification.
- Every singular modulus of degree at least five requires at least six terms, with five possible exceptions at discriminants −87, −131, −348, −432 and −675. Every modulus of degree at least seven requires at least six terms. At width at most 65,536 the five exceptions are excluded too. The unrestricted five-term status of those five orders remains open in this report.
- The minimum support is at least a constant times the class number divided by the square of the logarithm of the absolute discriminant, using Dirichlet GRH. An unconditional bound has exponent arbitrarily close to 1/2 − 1/(4√e). An explicit density-9/13 set has minimum support within O(log h) of h+1.
- An infinite explicit family attains the maximum possible minimum support h+1. Its first member has discriminant −2^44, degree 1,048,576 and minimum support 1,048,577. The exact-family theorem and the classifications above are independent of the zero theorem.

## Replay

From the extracted folder, with Python 3.8 or later and a GNU-compatible C++17 compiler available as `c++`, run

```sh
python3 verify.py
```

The driver uses Python's standard library. The older range checker uses the GNU-compatible 128-bit integer type. Set `CXX` to choose a different compiler. The driver uses temporary directories, runs with Python assertions enabled in the checkers, and checks the recorded outputs. It rebuilds the class polynomials in degrees four through eight and all exceptional finite-sieve inputs from integral interval enclosures. The 371-polynomial extended census uses 1,800 bits of interval precision. Allow several minutes on a desktop computer. The huge earlier discriminant range is checked by the earlier authors' modular sieves and counts.

The PDF can be rebuilt with a standard TeX Live installation including Latin Modern and microtype.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

Verify file integrity on systems with GNU coreutils using `sha256sum -c SHA256SUMS` from the extracted folder.

## File guide

| File or directory | Purpose |
| --- | --- |
| report.pdf, report.tex | Typeset paper and main LaTeX source |
| earlier.tex, five-term.tex, extremal.tex, width-note.tex, five-width.tex | Sections included by the main source |
| verify.py | Single-command verification driver |
| five/five_sieve.cpp, five/residual.txt, five/counts.txt | Exhaustive five-term reduction to 66 class polynomials below 23,059,204 |
| certificates/cm_gen.py | Reconstruct class polynomials by certified interval arithmetic |
| certificates/cm_order_census.py, certificates/cm_order_678_census.py | Census of orders of degrees 4–5 and 6–8 using published bounds for fundamental discriminants |
| certificates/cm_extra.py, certificates/cm_all_orders.py, certificates/cm_extended.py | Replay the local root counts, using exact integer and rational arithmetic |
| certificates/*.json | Monic class polynomials, constant coefficient first, keyed by absolute discriminant |
| certificates/*.csv | Local disk witnesses and the threshold and number of roots at each witness |
| certificates/cm_disk_limit.py | Eliminate every rational prime as a five-root single-disk witness at the five remaining discriminants |
| certificates/cm131_width.cpp | Independent first-exponent width check at −131 |
| certificates/cm_outlier_width.py, certificates/cm_outlier_width.cpp | Check the local hypotheses and all five width-65,536 exclusions |
| prior/ | Inherited analytic endpoint, reduced-form, complex interval, and discriminant sieve code and reference outputs |
| verification/ | Recorded outputs of the computations |
| SHA256SUMS | Digest of each other archive member |

## Provenance and scope

- The inspected Lean repository revision is `72fead102f663d5c7a407964a13dc0cf9d977207`. The external verification cited in the paper is Andrew Sutherland's replay. The present package contains conventional mathematical proofs and finite computational certificates for the CM results. [Upstream](https://github.com/lsernau/grh-lean) · [Verification files](https://math.mit.edu/~drew/shortgrh/)
- The starting ProveIt revision is `13c30b3b677b691845466289bfdb792d11fefad5`. Its incoming archive `grh_cm_prime_applications.zip` has SHA-256 `1ad1eb3b15a62ca4d04d0107fc151bec4681543baf69f612a786db3146dde01d`. The files in `prior/` are from this packet. [Incoming reports](https://github.com/VladimirReshetnikov/ProveIt/tree/13c30b3b677b691845466289bfdb792d11fefad5/docs/incoming)
- Another manuscript available during the analysis, *Sparse equations for singular moduli and the sign of weighted prime sums*, independently reaches the four-term classification. Its archive `grh_cm_four_terms_and_prime_bias.zip` has SHA-256 `47817f2addaa089194065bc676a6499331e057656d1f9d79264fa70a5ffb7308`. The paper identifies the overlap. Scholarly priority for the five-term and growth results has not been established.
