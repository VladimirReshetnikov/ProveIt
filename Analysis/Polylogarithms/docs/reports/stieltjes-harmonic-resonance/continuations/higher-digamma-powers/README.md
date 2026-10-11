# Higher Digamma Powers and Ordered Gamma Sums

Research continuation prepared for Vladimir Reshetnikov and ProveIt,
11 October 2026.

The complete article is
[Higher_Digamma_Powers_and_Ordered_Gamma_Sums.pdf](Higher_Digamma_Powers_and_Ordered_Gamma_Sums.pdf).
Its standalone source is
[Higher_Digamma_Powers_and_Ordered_Gamma_Sums.tex](Higher_Digamma_Powers_and_Ordered_Gamma_Sums.tex).

## Main results

- A normalized Mittag–Leffler formula and an exact original-coordinate
  finite-part formula for every positive integer power of the digamma function.
- An explicit boundary polynomial, with constant zero at odd powers and
  (-1)^m pi^(2m)/(2m+1) at power 2m.
- A terminating reduction to finite strict harmonic-word data, plus an
  alternative absolutely convergent series with explicit ordinary Stieltjes
  corrections at every power.
- The complete fifth-power finite part, including its mixed double-zeta
  derivative contribution, all scalar terms, and ordinary zeta derivatives.
- A fifth-degree polynomial that cancels the displayed lower height-one
  coefficients, explicit gamma_1 correction, and zeta'(3), while retaining
  the precisely defined mixed coordinate Omega_4.
- Normalized primitives and differentiated polygamma identities at all powers.
- An arbitrary-endpoint two-marker Gamma generator for ordered harmonic
  interpolation; finite reductions at every nonnegative integer marker gap;
  generalized Stieltjes and log-Gamma derivative consequences.
- A finite-interval formula with several tagged exponents and polylogarithmic
  depth cancellations at every negative integer marker.
- Two exact external-source corrections and a local S2 attribution improvement.

The fifth-power question in the incoming Quartic Tails report is answered.
The arithmetic reduction of the retained spectral constants, a full
single-coordinate canonical-polynomial theorem, and the current Gaussian S6
and revised S8 conjectures remain unresolved. The article states each limit
where it matters. Historical priority beyond the cited comparisons is not
claimed.

## Source baseline

Repository:
https://github.com/VladimirReshetnikov/ProveIt

Revision:
b7667ae40a2957eed9a53d8559d53a3ee20dd1c1

The inspected directories are Analysis/Polylogarithms/docs/manuscript and
docs/incoming. The source manifest includes SHA-256 hashes of the incoming
archives and selected manuscript files. The source audit is targeted; it is
not certification of all manuscript chapters.

## Rebuild and verify

Python 3, SymPy, and mpmath are required for the mathematical checks. The
recorded versions are SymPy 1.14.0 and mpmath 1.3.0. A standard TeX installation
with pdflatex and the packages declared in the source builds the article.

From this directory:

    python3 code/exact_checks.py
    python3 code/independent_fifth.py
    python3 code/verify_ordered_generators.py
    python3 code/build_article.py

The first command performs exact finite algebra, including coefficients through
power eight and the canonical fifth polynomial. It writes reusable word tables.
The second independently constructs the fifth algebra and compares local
subtraction quadrature with a Bernoulli/Hurwitz-tail calculation. The third
compares ordered Gamma identities with direct nested sums and independent
polylogarithm power series. Numerical checks are not interval certificates.

The build command assembles the editable tex_parts fragments, writes the
standalone TeX, and runs pdflatex three times. It rejects unresolved references,
LaTeX warnings, and overfull boxes. To rebuild only the standalone TeX without
using the fragments:

    pdflatex -interaction=nonstopmode -halt-on-error Higher_Digamma_Powers_and_Ordered_Gamma_Sums.tex
    pdflatex -interaction=nonstopmode -halt-on-error Higher_Digamma_Powers_and_Ordered_Gamma_Sums.tex
    pdflatex -interaction=nonstopmode -halt-on-error Higher_Digamma_Powers_and_Ordered_Gamma_Sums.tex

Do not make separate inconsistent edits to the fragments and assembled source.
The fragments are the editable source of record for the assembly script.

## Package map

| Path | Contents |
| --- | --- |
| Top-level PDF and TeX | Complete article and independently compilable source |
| tex_parts/ | Modular source for integration and revision |
| code/ | Exact algebra, independent numerical verification, build script |
| data/ | Exact coefficient tables and verification receipts |
| integration/ | Placement notes, claim ledger, source hashes, corrections |
| validation/ | Build and visual-review records |
| exploratory/S6_depth5_bounded_search.zip | Reproducible bounded Gaussian relation experiment |
| SHA256SUMS | Integrity manifest for the deliverable files |

## The S6 investigation

The optional search package specifies 22,296 integer rows in 8,786 imaginary
word coordinates at weight seven and maximum input depth five. A complete
elimination over F_2147483647 found rank 8,705 and a nonzero 16-coordinate
target. This is nonmembership in that specified finite-field row span.
It is not rational-span nonmembership and is not nonvanishing of the period
residual. The underlying conjecture is not proved or disproved.

The search code requires a C++17 compiler; its separate README records the
exact family, target normalization, source provenance, and reproduction
commands. No experimental result is used to prove the article's identities.

## Integration

Start with [INTEGRATION.md](integration/INTEGRATION.md) and
[CLAIM_LEDGER.json](integration/CLAIM_LEDGER.json).
The manuscript was not modified as part of preparing this package.
Preserve the original-coordinate finite-part convention, the distinction
between kappa_k and C_k, and the Laurent-coefficient definition of D_(1,3).
