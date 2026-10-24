# A self-bounding factorial certificate

## Theorem

For natural `n,m`, define `q=m n^2`, `c=binomial(q+n,n)`, and
`p=(q+1)^n`. Then

    m=n!  iff  m=ceil(p/c).

Equivalently, `m=n!` holds exactly when there are natural `r,s` with

    p+c = mc+r+1,
    c = r+s+1.

This replaces the previous radius `(n+2)^(n+2)` by the polynomial radius
`m n^2`. It removes one ordinary positive-power macro from every
factorial call; the radius needs at most two product registers before
any global sharing. No exponentiation is eliminated by notation: the
remaining binomial and power calls must still be compiled literally.

## Exact interpretation of the rows

Always `c>=1` and `p>=1`. The two rows say

    p = c(m-1)+(r+1),   1<=r+1<=c.

They are therefore exactly `m-1 < p/c <= m`. In particular `m>=1`:
if `m=0`, then the first row gives `p+c=r+1<=c`, contradicting `p>=1`.

Conversely, if `m=ceil(p/c)`, choose `r=p+c-mc-1` and
`s=c-r-1`. The ceiling inequalities prove both are natural and give
the displayed equations.

## Ratio estimate

If `n=0`, then `q=0`, `c=p=1`, and the assertion is immediate.
Now suppose `n>=1` and `m>=1`; thus `q=mn^2>=1`. Write `F=n!` and

    R = p/c = F product_(i=1)^n (q+1)/(q+i).

Every factor lies in `(0,1]`, so `0<R<=F`.
Set `d_i=(i-1)/(q+i)`. These are numbers in `[0,1)`, and

    sum_i d_i <= n(n-1)/(2q) < n^2/(2q) = 1/(2m).

(The first inequality can be made strict for `n>=2`, but is not needed.)
The elementary finite-product inequality
`product_i(1-d_i) >= 1-sum_i d_i`, proved by induction, yields

    R > F(1-1/(2m)).                         (1)

## Soundness

Assume `m=ceil(R)`. Since `F` is an integer and `R<=F`, we have `m<=F`.
Also `R<=m` and (1) give

    F < m/(1-1/(2m))
      = m + m/(2m-1)
      <= m+1.

The final inequality uses `m>=1`; its equality case `m=1` is harmless
because the first inequality is strict. As `F` is an integer,
`F<=m`. Therefore `F=m`.

## Completeness

Put `m=F`. Then (1) becomes `R>F-1/2>F-1`, while `R<=F`.
Hence `ceil(R)=F`, and the natural remainder/slack witnesses above exist.

## Positivity of nested power calls

For the positive-only compiler, `n>=1` is the already established
factorial-input invariant. Even before factorial correctness is recovered,
`q=mn^2>=0`, so `q+n>=1` and `q+1>=1`. The binomial macro's upper
argument is `q+n`, its lower argument is `n`, and the remaining direct
power has exponent `n` and base `q+1`. They are all positive independently
of the unknown candidate output `m`. Thus using the positive-power macro
is sound even on a hypothetical spurious tuple with `m=0`; the ceiling
rows subsequently rule that case out.

There is no circularity: power and binomial graphs are first calibrated
pointwise. The displayed arithmetic inequalities then identify the
factorial output.

## Suggested implementation change

Keep allocating the factorial output before its radius. Replace only

    shifted = self.add(n, TWO)
    radius = self.power(shifted, shifted)

by

    radius = self.mul(out, self.square(n))

Keep the binomial, numerator and two ceiling/remainder rows unchanged.
The original all-natural macro also works for `n=0`; an exclusively
positive-power implementation should continue to rely on its existing
positive factorial-input invariant.
