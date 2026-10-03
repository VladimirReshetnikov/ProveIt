# Draft OEIS comments — not submitted

These are proposed comments for review, not notices of accepted OEIS updates.
The accompanying article should be independently checked before submission.
Leading formulas must retain their existing attribution.

## A238016 / general condition also appearing in A258670

A precise stronger condition is f(n)/n^3 -> infinity, under which the count is
asymptotic to f(n)^(n-1)/(n!*(n-1)!). Sufficiency is a classical consequence
of the Erdos-Lehner estimate recorded in Step 5 of Canfield (1997),
DOI 10.37236/1321. The report gives an elementary proof and proves necessity
as well: for positive integer f(n), the volume ratio tends to 1 if and only
if f(n)/n^3 tends to infinity. At f(n)~c*n^3 the ratio tends to exp(1/(4c)).

This avoids treating the original notation f(n)>=O(n^4) as a standard
mathematical inequality and avoids attributing a classical consequence as a
new result.

## A238608

The posted leading expression can be refined to

    a(n) = exp(2*n+1/4)*n^(n-3)/(2*pi) *
      (1 - 61/(288*n) - 37463/(165888*n^2)
         + 425075267/(3583180800*n^3) + O(n^-4)).

The report derives two more terms, an all-order recurrence with a uniform
remainder theorem, and an inverse asymptotic chart. The leading expression
is already present in the entry and is not newly attributed here.

## A238010 / fixed integer column q>=2

For a_q(n)=p_n(q^n), the logarithm has the refinement

    log(a_q(n)) = n*(n-1)*log(q) - log(n!) - log((n-1)!)
      + n*(n^2-1)/(4*q^n)
      - n*(n^2-1)*(13*n^2+3*n-4)/(288*q^(2*n))
      + O(n^9*q^(-3*n)).

The exact factorial background should be retained when identifying these
exponentially small corrections. A finite Stirling truncation would have an
algebraic error larger than the corrections being displayed.
