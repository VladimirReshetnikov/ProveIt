# Source and contribution audit

Audit date: October 1, 2026. This is a targeted source comparison, not an
exhaustive literature or repository search.

## OEIS A279619

Source: https://oeis.org/A279619/internal

The displayed revision was August 22, 2026. The entry supplies the quadratic
recurrence, the relation to the square root of the generating function for
A183204, and the identification with Theorem 6.1 of O'Brien's thesis. It
labels the leading asymptotic conjectural and provides a decimal constant.
A hypergeometric generating function is given in Wolfram Language code
credited to Vaclav Kotesovec on July 4, 2018. We did not discover that
representation; we rationalized and certified it before extracting its
connection coefficient.

The entry separately states a Lucas-congruence conjecture. That arithmetic
statement is not resolved by this report. A functional identity added in
August 2026 is a possible future input, not a dependency of the present proof.

## O'Brien's thesis

Lynette O'Brien, *Modular forms and two new integer sequences at level 7*,
Massey University MSc thesis, 2016.
https://oeis.org/A279619/a279619.pdf

The thesis is the primary source for the sequence. Section 8.4 discusses
its asymptotics. Printed pages 66–67 (PDF pages 73–74, one-based) give the
formal expansion and the coefficients -215/1008, -1265/290304, and
4683055/877879296. These are explicitly credited, not advertised as new.
The report's proof supplies a controlled remainder and identifies the
constant in gamma-product form.

## Two classical special-value inputs

1. Ralf Hemmecke, Peter Paule, Cristian-Silviu Radu,
   *Computer-assisted construction of Ramanujan–Sato series for 1 over pi*,
   manuscript dated January 31, 2025.
   https://www3.risc.jku.at/publications/download/risc_7134/.RamanujanSatoOneOverPi.pdf

   Equation (98), printed page 32, gives the level-seven Ramanujan series.
   The paper itself notes its earlier appearance in Ramanujan's work.
   Converting its factorial coefficient to Pochhammer notation gives
   (8+133 theta) 3F2(1/6,1/2,5/6;1,1;64/85^3)
   =85 sqrt(255)/(54 pi). The report checks the normalization explicitly.

2. J. M. Borwein and I. J. Zucker,
   *Fast evaluation of the gamma function for small rational fractions using
   complete elliptic integrals of the first kind*, IMA Journal of Numerical
   Analysis 12 (1992), 519–526.
   https://academic.oup.com/imajna/article-abstract/12/4/519/690281

   The explicit beta-function version for K[7] was inspected in Table 1 of
   Zucker's singular-value exercise notes in Jonathan Borwein's archive:
   https://carmamaths.org/jon/Preprints/Books/EMA/Exercises/For%20others/K-beta.pdf

   The table fixes k_7^2=(8-3 sqrt(7))/16. Appendix A uses gamma duplication
   to convert its beta expression to Gamma(1/7)Gamma(2/7)Gamma(4/7) /
   (4 pi 7^(1/4)). We treat the classical table evaluation as an established
   special-value input, not as a new theorem or a numeric guess.

The relevant PDF equations and table were checked as rendered page images,
not only through garbled mathematical text extraction.

## Other analytic inputs

The Gauss hypergeometric differential equation and gamma-ratio asymptotics
are standard; the report cites DLMF sections 15.10 and 5.11. DLMF 4.13
provides Lambert-W branch conventions. Singularity transfer is cited to
Flajolet and Sedgewick, *Analytic Combinatorics* (2009), Chapter VI.

The report verifies the hypotheses needed here: a nonzero square-root
connection coefficient, a convergent local Frobenius expansion, and a
dented analytic continuation domain with no competing singularity on the
dominant circle. Formal recurrence fitting is not substituted for these
analytic arguments.

## A183204

Source: https://oeis.org/A183204/internal

The square generating-function relation and leading asymptotic are existing
results. The report recovers the leading term, gives the first correction,
and proves a fixed-integer convolution theorem. The symmetric-square ODE
is checked as an exact rational identity. Finite binomial-sum comparisons
in the program serve as independent computational diagnostics.

## Related recent work, not a proof dependency

Henri Cohen and Wadim Zudilin,
*Continued Fractions and Irrationality Measures for Chowla–Selberg Gamma
Quotients*, arXiv:2510.00215, first submitted in 2025 and revised in 2026.
https://arxiv.org/abs/2510.00215

This shows that continued fractions involving gamma quotients are an active
and developed topic. We do not claim a first such continued fraction. The
comparison made here does not settle whether the particular limit L or a
transformation of its recurrence has already appeared in that literature.

## ProveIt inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: a5ad4ac2e2d4e642a6c015836a70492d40fcbc71
Inspected organization: Analysis/Transseries/README.md, relevant directory
metadata, and a targeted GitHub search for A279619.

The targeted code search returned no result for A279619. This does not
establish absence from every archived PDF or ZIP. The transseries README
motivated the separation into analytic existence, coefficient calculus, and
inversion. No unverified repository theorem is a dependency of this report,
and no repository changes were made.

## Claims established in the report

- Exact gamma-product leading constant and boundary sum.
- Dominant expansion to every fixed order with a next-order remainder.
- Exact rational Wronskian, continued fraction, and alternating rational bounds.
- An actual recessive solution with exact gamma-product amplitude and
  all-order rational corrections.
- Convolution-power expansions and a coefficient-field statement.
- Formal inverse algorithm, asymptotic validity, and discrete rounding brackets.

The accompanying code checks the algebra and supplies interval certificates
and diagnostics. It is not a complete formal verification of the article.

## Claims deliberately not made

- Global first-publication priority for every formula.
- Resolution of Lucas congruences.
- Irrationality of L or an irrationality measure.
- A closed special-value expression for L.
- A canonical Borel-summed or exponentially improved transseries for a(n).
- Convergence of the series in 1/n.
- Explicit numerical remainder constants valid for all sufficiently large n.
- Existing Lean certification of the analytic or complex-multiplication steps.
