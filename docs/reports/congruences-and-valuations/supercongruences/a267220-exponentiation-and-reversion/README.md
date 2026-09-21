# Apéry numbers under exponentiation and series reversion

**Result:** proofs of both supercongruence conjectures contributed by Peter Bala to OEIS A267220 on 17 October 2024. The underlying numbers are the classical Apéry numbers, OEIS A005259.

Prepared 20 September 2026. The article is a mathematical research exposition, not a formally verified or peer-reviewed publication. It explicitly credits the existing framing theory of Schwarz, Vologodsky, and Walcher. An OEIS conjectural label is not a guarantee of literature-wide novelty. No changes have been submitted to OEIS.

## Mathematical contents

Let

    a_n = sum_{k=0}^n binomial(n,k)^2 binomial(n+k,k)^2,
    G(z) = exp(sum_{n>=1} a_n z^n/n),
    F(w) = w / Rev(z G(z))(w),
    u_m(n) = [z^n]G(z)^(m n),
    v_m(n) = [w^n]F(w)^(m n).

The two conjectures assert, for every integer m, every prime p >= 5, and positive n,r,

    u_m(n p^r) == u_m(n p^(r-1)) mod p^(2r),
    v_m(n p^r) == v_m(n p^(r-1)) mod p^(2r).

Both are proved. The first holds for every odd prime; the second holds for every prime, including 2. The article also proves stronger parameter-sensitive bounds and integrality of

    B_t(n) = [z^n]G(z)^(t n)/t  (t != 0),
    B_0(n) = a_n.

The exact identities are u_m(n) = m B_m(n) and v_m(n) = m B_(m-1)(n), for n >= 1. The bounds apply to negative, zero, and positive integer parameters, with the zero case stated separately when taking valuations.

The main proof consists of an elementary binomial-product congruence, an integral Euler product, Lagrange inversion, and an explicit formal Frobenius-defect calculation. It does not rely on a computer search or on the stronger classical order-three congruence for the Apéry seed.

Two overstatements are explicitly refuted: a uniform extension of the first family to p=2, and a uniform replacement of the exponent 2r by 3r in either family.

## Artifact inventory

| File | Purpose |
| --- | --- |
| `article.pdf` | Complete typeset article with proofs, examples, computational audit, and references. |
| `article.tex` | Self-contained LaTeX source; bibliography is embedded, with no separate BibTeX run. |
| `verify.py` | Exact integer/rational verification program, Python 3.10 or later, standard library only. |
| `data/verification_summary.json` | Machine-readable counts and exact counterexamples from the saved run. |
| `data/validation_log.txt` | Saved standard output of the verification command. |
| `data/odd_prime_checks.csv` | 798 normalized checks, including actual valuations and scaled differences. |
| `data/sample_coefficients.csv` | Apéry numbers and related coefficients at indices 1 through 20. |
| `sources.md` | Source metadata, links, and the distinction between prior results and this application. |
| `proposed_oeis_note.md` | An unsubmitted short mathematical note suitable for adaptation to an OEIS update. |

The archive deliberately excludes compilation intermediates, preview images, downloaded third-party papers, and font files.

## Reproduce the exact checks

Run from this directory:

```sh
python3 verify.py --out data --limit 150
```

No installation from PyPI is required. Run without Python's `-O` option; the program refuses to run with its verification assertions disabled.

The saved run checks the Apéry binomial sum against the standard recurrence at every index from 0 through 150. It checks 269 seed congruences, 798 normalized odd-prime congruences, 1,575 normalized two-adic bounds, 840 parameter-sensitive odd-prime bounds for the exponential family, 1,575 parameter-sensitive two-adic bounds for that family, and 2,415 bounds for the reverted family including the prime 2.

Separate rational-series routines construct the compositional inverse directly and check 126 reversion-and-power identities. They also check 18 full Frobenius-defect identities through degree 14. These independent routines avoid generating both sides of the reversion identity from the same parameter-shift shortcut.

All checks passed. The exact grids are documented in section 10 of the article and in the code; this does not mean every possible integer parameter or prime below every bound was tested. Finite checks support the implementation and examples; the article's proof establishes the infinite statements.

The program writes to the directory passed by `--out`, replacing its generated CSV/JSON files. A larger limit extends the available index range and some grids, but the prime and framing-parameter lists remain the explicit lists in the code. No external account or network access is used.

## Rebuild the PDF

A standard TeX Live or MiKTeX installation containing the packages named in `article.tex` is sufficient. The preferred build command is:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` repeatedly until there are no cross-reference rerun warnings, usually two or three passes. The distributed PDF has resolved references and was rendered for visual inspection.

## Reading route

Sections 1–2 specify the exact conjectures and strengthened conclusions. Sections 3–7 contain the proofs. Section 8 records explicit counterexamples to stronger variants. Section 9 explains the generalization to even binomial moments. Section 10 documents computation and reproduction. Appendix A proves the Lagrange formula; Appendix B records the dependency and edge-case audit.
