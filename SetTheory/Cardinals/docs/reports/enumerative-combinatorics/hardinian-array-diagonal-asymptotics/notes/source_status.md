# Source and open-status ledger

Search/access date: **19 September 2026**.

This ledger records what was actually consulted. An unsuccessful search for a
prior proof is not evidence that no prior proof exists. The article's proposed
resolution is unrefereed, and no external updates or submissions were made.

## Selected conjecture and combinatorial input

Robert Dougherty-Bliss and Manuel Kauers, **Hardinian Arrays**,
Electronic Journal of Combinatorics 31(2) (2024), Paper P2.9, 13 pages.
DOI: https://doi.org/10.37236/12358
Published PDF:
https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i2p9/pdf
Preprint: https://arxiv.org/abs/2309.00487

The published PDF was read, including rendered images of the relevant page.
The proof of Theorem 6 (printed p.9) uses the all-r complementary-minor formula.
Printed p.12 explicitly proposes H_r(n,n) ~ c 2^(2rn) n^(-binom(r,2)), and
suggests that c is a power product of 2, 3, and pi. Its table lists r=0..5.
The published paper proves D-finiteness for all fixed-r diagonals and the
particular guessed recurrence at r=2; those results are not new claims here.

The first part of the conjecture is proved by the supplied manuscript. The
arithmetic restriction is contradicted at r=7 under its meaningful integer- or
rational-exponent interpretation.

## OEIS entries and independent reference values

A253217: https://oeis.org/A253217
Reference terms: https://oeis.org/A253217/b253217.txt

The retrieved entry still labels the asymptotic
2^(4n-2)/(81*pi*n) as a conjecture attributed to Vaclav Kotesovec, 2 March 2023.
The entry separately notes the proof of its recurrence. These are not the same
claim. All n=1..37 reference values were transcribed and compared exactly.

A252998: https://oeis.org/A252998
Reference terms: https://oeis.org/A252998/b252998.txt

This is the r=3 diagonal. The b-file was read through n=101. The stored
independent check set comprises n=1..30,40,70,100,101. No claim of checking every
one of the 101 terms is made. The reference values in the archive are explicitly
marked as transcriptions from the retrieved sources, not as successful direct
network downloads into the container.

## Later related work

Robert Dougherty-Bliss and George Spahn, **Rectangular Hardinian Arrays**,
ACM Communications in Computer Algebra 58(3), 81–84.
https://doi.org/10.1145/3717582.3717589

Publisher record/abstract consulted. It records online publication on
11 February 2025 (the issue itself is labelled September 2024). The abstract
states eventual polynomiality in n for fixed r and fixed width k, using a
transfer-matrix method. That statement concerns a different asymptotic regime.
The full proof was not used, and this ledger does not assert a complete review
of everything in that article.

## Classical technical references

N. G. de Bruijn, **On some multiple integrals involving determinants**,
Journal of the Indian Mathematical Society (N.S.) 19 (1955), 133–151.
Primary institutional publication record:
https://research.tue.nl/en/publications/on-some-multiple-integrals-involving-determinants/

The record was consulted for attribution/bibliography. The specific
ordered-determinant/Pfaffian identity required here is independently proved in
the manuscript, including its odd-dimensional and discrete versions.

Liviu I. Nicolaescu, **A probabilistic computation of a Mehta integral**,
arXiv:2408.06203 (submitted 12 August 2024).
https://arxiv.org/abs/2408.06203
https://arxiv.org/html/2408.06203v1

Abstract and HTML were consulted for context and the Gaussian normalization.
The manuscript supplies its own Hermite/Pfaffian evaluation rather than relying
on this paper's proof. The date in an auto-rendered HTML header was not used as
an independent publication-history claim.

## Search limitation

Web searches included the exact Hardinian-array name together with asymptotic,
Pfaffian, Gaussian, and later-paper terms. No all-r diagonal constant formula
or prior proof was located in the material returned. Some search queries
returned irrelevant pages and were not evidence either for or against novelty.
No comprehensive MathSciNet/Zentralblatt/citation-index search or direct author
confirmation was performed. The OEIS conjecture label is evidence of how the
retrieved entry describes the problem, not a guarantee against an unindexed or
unincorporated solution elsewhere.
