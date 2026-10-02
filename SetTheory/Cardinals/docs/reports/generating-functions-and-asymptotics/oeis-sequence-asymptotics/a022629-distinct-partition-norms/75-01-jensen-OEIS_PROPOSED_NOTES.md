# Draft OEIS notes — not submitted or approved

These are proposed additions for review, not a representation of an OEIS edit.
The supporting report is `article.pdf` in this package. Independent mathematical
review and a publication-level literature check should precede a priority claim.

## A022629: growth and refinements

Let N = sqrt(2*n), L = log(N). The report proves

    log(a(n)) = N*(L - 1) + O(N/L).

This implies the conjectural equivalence attributed in the entry to Vaclav
Kotesovec, May 8, 2018, and also identifies the second term -N.

A stronger expansion is

    log(a(n))/N = L - 1
      + pi^2/(6*L)
      + pi^2/(6*L^2)
      + (pi^2/6 - pi^4/72)/L^3
      + (pi^2/6 + pi^4/40)/L^4
      + (pi^2/6 + 41*pi^4/180 + pi^6/432)/L^5
      + O(L^(-6)).

The report gives an all-order coefficient prescription and a distinct,
finer, relative-error expansion based on the exact saddle. Exponentiating a
fixed truncation of the display above does not give relative error tending
to zero.

## Eventual shape

The report proves eventual strict log-concavity and

    log(a(n)^2/(a(n-1)*a(n+1)))
      ~ log(sqrt(2*n))/(2*n)^(3/2).

Every Jensen polynomial of a fixed degree is eventually hyperbolic.
The latter assertion follows by verifying the hypotheses of the known
Griffin–Ono–Rolen–Zagier Hermite-limit mechanism; that mechanism is not new.

Exact computation finds strict log-concavity for every n = 77,...,9999 and a
failure at n = 76. This finite test does NOT prove that 77 is the global
minimal threshold.

## A292189 and positive columns

For each fixed positive real s, the same theorems apply to coefficients of
product_{k>=1}(1+k^s*q^k). In the displayed logarithmic expansion replace
log(a(n))/N with log(a_s(n))/(s*N), and every pi^(2*j) with
(pi^2/s^2)^j. The shape equivalent acquires a factor s.

For positive integers s = 1,...,5, these are A022629, A092484, A265840,
A265841, and A265842. This fixed-parameter result does not cover s = 0 or
the diagonal s = n.

Source records consulted: https://oeis.org/A022629 and
https://oeis.org/A292189, accessed October 1, 2026.
