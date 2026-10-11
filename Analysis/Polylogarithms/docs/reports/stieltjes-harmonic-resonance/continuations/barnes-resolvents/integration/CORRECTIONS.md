# Precisely scoped correction

## External source

István Mező, *The Fourier series of the log-Barnes function*,
arXiv:1604.00753v1 (2016), equation (7), printed page 6
(the sixth PDF page; zero-based page index 5).

Source: https://arxiv.org/pdf/1604.00753v1

The displayed pointwise identity has left side `log(G(x))^2` and
right side one quarter of the sum of the squared logarithms of
`G(x)G(1-x)` and `G(x)/G(1-x)`.

## Exact correction

Set `a=log G(x)`, `b=log G(1-x)` for `0<x<1`. The right side is

    ((a+b)^2 + (a-b)^2)/4 = (a^2+b^2)/2.

Replace the pointwise left side by

    (log(G(x))^2 + log(G(1-x))^2)/2.

Alternatively, keep the old left side and add

    log(G(x)G(1-x))*log(G(x)/G(1-x))/2

to the right side. The corrected LaTeX equation is labeled
`bhr:eq:Mezo-correction` in the article.

This is demonstrably a pointwise error: as `x` approaches zero,
`G(x)=x*(1+O(x))` and `log G(1-x)=O(x)`. The original left side
has leading term `log(x)^2`, while the original right side has
leading term `log(x)^2/2`.

## Consequence

The integrated identity over `(0,1)` is valid by reflection.
The extra product above is antisymmetric under `x -> 1-x`, and
the two squared log-G integrals are equal. Therefore this correction
does not refute the integrated theorem that follows the printed line.
It is sufficient to symmetrize the pointwise left side or to place
the equality after integration.

The numerical program records the nonzero pointwise residual at `x=1/4`
as a diagnostic, approximately `0.7368670117345925017455509188586147`.
The algebraic and endpoint arguments, not that decimal, prove the correction.

## Repository scope

No new mathematical error in the inspected repository material was
established. This correction concerns the cited external source version.
The existing distinction between the rejected old S8 vector and the
current revised S8 conjecture should be preserved exactly.
