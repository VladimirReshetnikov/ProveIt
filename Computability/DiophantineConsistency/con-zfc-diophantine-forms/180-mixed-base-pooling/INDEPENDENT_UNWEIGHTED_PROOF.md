# Unweighted reciprocal pooling with signed bases

Independent extension, 25 October 2026. The enormous retained Pell height
permits a second integrality argument, eliminating the orientation factors
from the reciprocal-pooling polynomial. This improves the five-base
degree bound from 24 to 22 after taking a sum of residual squares.

## Theorem

Keep the same notation, canonical Pell interface, square-frame bounds and
definitions `T_j,H_j,S_j,E_j` as in `INDEPENDENT_POOLING_PROOF.md`. Bases may
be zero and have arbitrary signs. Let `W>=258`, `|A|>W^W`, and
`b=floor(sqrt(W-1))`. Suppose `4r<W` and

    (s+1)b + ceil((s+1)/2) + 1 <= W.

These inequalities hold uniformly for `s<=14` and `r<=64`.

Then all divisibilities `T_j|E_j` are equivalent to existence of an integer
`z` satisfying the UNWEIGHTED polynomial equation

    sum_j E_j product_{h != j} T_h - z product_h T_h = 0.       (U)

They are also equivalent to all nonzero-base requests being exact signed
rational powers. Singleton congruence blocks `delta+TQ=0` can replace
aggregate divisibility blocks, with the same restoration proof as in the
oriented theorem.

## Proof: first integrality step

All moduli are nonzero: a zero base gives `T_j=-1`, and a nonzero base has
`|T_j| >= (2|A|-W)|n_j| > W^W`. Also `sign(n_j T_j)=sign(A)`.

The identity

    sum_{i in I_j} delta_i^2 = E_j-T_j sum_{i in I_j}Y_i^2,
    delta_i=m_i-X_i+(A-n_j)Y_i,

shows that (U) makes `sum_j sum_i delta_i^2/T_j` integral. Zero-base
terms are already integers, so discard those blocks. If none remain,
the desired divisibilities are automatic. Otherwise let `J` be the set
of remaining blocks, `s'=|J|`, and put

    C=(product_{j in J} n_j)^b,
    d_i=C m_i-(C/n_j^b)n_j^{b+k_i},
    D_j=sum_{i in I_j}d_i^2.

As in the oriented proof, all `d_i` are integers and
`C delta_i == d_i (mod T_j)`. Therefore

    R=sum_{j in J} D_j/T_j

is an integer. Set `D=sum_j D_j`. The earlier bounds give

    D <= 4r b^{2(s+1)b}.

The stronger estimate established below implies `D<W^W`, so
`|R| <= D/(2|A|-W)<1`, hence `R=0`.

Unlike the oriented argument, this zero rational sum can have summands
of both signs. The next step excludes their cancellation using a second
integer whose absolute value is less than one.

## Proof: second integrality step

Let `L=product_{j in J} n_j`, a nonzero integer. The exact identity

    2A/T_j = 1/n_j + (n_j^2+1)/(n_j T_j)

and `R=0` give

    U+V=0,
    U=sum_j D_j/n_j,
    V=sum_j D_j(n_j^2+1)/(n_j T_j).

Now `LU` is an integer. Since `LV=-LU`, so is `LV`. On the other hand,
the weighted denominator bound and `|n_j|>=1` imply

    (n_j^2+1)/|n_j T_j|
       <= (1+n_j^(-2))/(2|A|-W)
       <= 2/(2|A|-W).

Consequently

    |LV| <= 2|L|D/(2|A|-W).

The numerator is small enough:

    2|L|D <= 8r b^{2(s+1)b+s}
            <= 4r b^{2(s+1)b+s+1}
             < W^{(s+1)b+ceil((s+1)/2)+1}
            <= W^W.

Here `2<=b`, `b^2<W`, and `4r<W` were used. This proves `|LV|<1`.
Thus `LV=0`, and since `L!=0`, also `V=0`. Every nonzero summand of `V`
has sign `sign(A)`, because `D_j>=0`, `n_j^2+1>0`, and
`sign(n_j T_j)=sign(A)`. Therefore every `D_j=0`, hence every `d_i=0`.

The canonical-Pell congruence now gives exactly the same conclusions and
integral restorations as in the oriented theorem. For nonunit bases the
indices must be nonnegative; unit bases allow signed indices; zero-base
divisibilities are automatic. Conversely every original divisibility
makes `z=sum_j E_j/T_j` an integer and satisfies (U).

Finally, `b>=16`; if `s<=14`, then

    (s+1)b+ceil((s+1)/2)+1 <= 15b+9 <= b^2+1 <= W.

The middle inequality follows from `b^2-15b-8>=8` at `b=16` and its
increase for larger integers. Also `r<=64` gives `4r<=256<W`.

## Degree and witness count

With affine bases and retained affine `Z_i=AY_i` coordinates, each `T_j`
is quadratic and each `E_j` is at most cubic. Equation (U) has degree at
most `2s+1`. Its square therefore has degree at most `4s+2`. It still
replaces `2s` private coordinates by one, saving `2s-1` coordinates.

For `s=5`, this is a nine-coordinate reduction at degree at most 22.
If every modulus has a nonzero homogeneous quadratic part and the new
variable `z` appears nowhere in the other terms, the coefficient of `z`
is minus the product of the five moduli, which has degree exactly 10.
Then the new residual has degree exactly 11 and its square exactly 22.
Other residual squares of degree at most four cannot cancel that leading
term.

## Why an extra argument is necessary

Without a sufficient height bound, unweighted cancellation is real. For
`A=2`, bases `1` and `-1` have moduli `2` and `-6`; numerators `D_1=1`
and `D_2=3` give `D_1/2+D_2/(-6)=0`. Both numerators are sums of squares,
yet neither is zero. The second integrality step excludes this phenomenon
at the retained large Pell height. This example does not satisfy the
theorem's height assumptions and is included as a negative control.

## Status

This is a complete ordinary arithmetic proof and a relative transformation
of an authenticated source system. It requires no additional coefficient
tuple or unknown and no coprimality or positivity assumption on the bases.
It makes no assertion of literature-wide novelty or of a newly checked
Lean/Rocq consistency calibration.
