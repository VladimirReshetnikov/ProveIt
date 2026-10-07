# Public source guide

Mathematical source observations were checked on 5 October 2026.

## Sequence definitions and observed refinements

- OEIS A360592: https://oeis.org/A360592
- OEIS A360479: https://oeis.org/A360479
- OEIS A360747: https://oeis.org/A360747

The exact sums match p=1,2,3 in the article. A360479 was retrieved directly;
A360592 and A360747 were obtained from indexed primary OEIS text when ordinary
opening was unreliable. Independent retrievals corroborated the formulas.
The article gives normalized transcriptions and coefficient differences.
No raw HTML snapshot or revision-history export is presented as part of this
package. Latest sequence revision identifiers and full histories were not
verified. Global footer dates and indexed modification dates cannot substitute
for revision identifiers.

Observed attributions: A360592 names Vaclav Kotesovec (13 February 2023).
A360479 and A360747 name Seiichi Manyama (19 February 2023) as sequence author;
their refinements are attributed to Kotesovec on 19 and 20 February 2023.
All three leading equivalents remain valid when '~' is interpreted literally.
The audit concerns the displayed intended higher-order coefficients.

## Classical background checked

- DLMF 1.10(vii), inverse functions and Lagrange inversion:
  https://dlmf.nist.gov/1.10.vii
- DLMF 18.23.5, Charlier generating function:
  https://dlmf.nist.gov/18.23.E5
- Corless, Gonnet, Hare, Jeffrey and Knuth, On the Lambert W Function,
  Advances in Computational Mathematics 5 (1996), 329-359:
  https://doi.org/10.1007/BF02124750

The DLMF statements were inspected. The Corless reference was verified at the
bibliographic/definition-level abstract; the complete article was not needed
for or represented as a sequence-specific source. The present inverse estimates
and required probability identities are proved in the article.

## Bounded prior-work checks and unresolved source

Two public default-branch catalogues inspected during screening were:

- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/README.md
  Git blob 88be777b257942b333e1e1b034165e006b0f2701
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/Transseries/docs/series-and-transseries/README.md
  Git blob b0f627c03c6f9e6aee9670d90cfa3a34c30710ad

Exact A-number/code and formula-oriented searches did not identify a duplicate
endpoint treatment. These bounded checks do not establish semantic absence or
universal priority.

Kotesovec's potentially relevant 2013 note, Interesting asymptotic formulas for
binomial sums, was bibliographically identified at
https://www.kotesovec.cz/math_articles/kotesovec_interesting_asymptotic_formulas.pdf
but retrieval timed out and its theorem content was not compared. No further
historical conclusion is inferred from that absence of access. The correction
is proved directly from the exact sums, independently of priority.
