# Independent arithmetic review: inverse-Lucas correction

Scope: review the replacement of the rank correction in the incoming Lucas
Corrections compact equation by an abscissa correction. The incoming
`compact/PROOF.md` was read. This note does not review its inherited Pell,
ratio, or native/refutation calibration theorems afresh. The review is a
separate AI-assisted workstream, not external human peer review.

## Conclusion

The replacement is sound with the following explicit proof order: full
`q^6` recovery is postponed until after projection proves `q` a power of 2. It is **not** valid to inherit the old proof that the new corrected error
is divisible by `q^6` immediately after first-index authentication.

Write `v=XY^2=q^3 w s^2`, `k=2 psi_(1+2v)(m)`, and replace the incoming error by

    e6 = 6(k-R-1) - v k(k^2-4),
    ebar = e6/6.

Keep `D6=6q^6`, the literal carrier shift `6q^4 s`, `X=qw`, `Y=qs`, and all
other definitions. The quotient ebar is proof notation only.

## 1. Integrality and the exact inverse identity

First norm classification makes `k` even. Therefore `k(k^2-4)/6` is integral:
putting `k=2u`, the quotient is `(4/3)u(u-1)(u+1)`. Thus ebar is integral
at every zero, without any assumption on R or any modular inversion of 6.

The retained finite Lucas expansion gives

    k = t + 8v C + 32v^2 Z,
    t=2m, C=binom(m+1,3), Z in Z_{≥0}.

Set

    A_m=C+4vZ,
    S=k^2+kt+t^2-4,
    d=t-R-1.

Then the following exact identity holds:

    3(ebar-d) = 4v^2(24Z-A_m S).                 (I)

Indeed, multiply the left side by 2, use
`v t(t^2-4)=48v C`, and factor
`k(k^2-4)-t(t^2-4)=(k-t)S=8v A_m S`.
This is a polynomial identity once the displayed relation for k is
substituted. No inverse-series convergence or infinite argument is needed.

## 2. Index authentication

Integral z and the carrier imply

    q^6 | hH(ebar-q^4s).

Since `h=q-1` and `H=4Y(X+1)-1=-1 mod q`, this gives
`q^6 | ebar-q^4s`, hence `q^4 | ebar`.
By (I), `q^6 | 3(ebar-d)`. For a prime ell dividing q, write
`a=valuation_ell(q)>=1`. Then

    valuation_ell(ebar-d) >= 6a - valuation_ell(3) >= 4a.

Thus `q^4 | ebar-d`, and therefore `q^4 | d`. The incoming base-monotonicity
argument gives `1<=m<R` and hence `|d|<R<q^4`. Consequently `d=0`.
Unlike the forward correction, there is no need for an intermediate
`q^3 | d` step.

## 3. Projection before full denominator recovery

Modulo H, the literal numerator is `Znum = 6h q^6 K`. Integral z gives
`H | Znum`, so, since `gcd(H,q)=1`,

    H | 6hK.

Apply the unchanged universal projection identity to get

    H | 6h(X-2^R)(2^R X+1).

The authenticated indices license the retained ratio lemma, giving
`X^(r+1)<H` for `R=2r+1`, `r>=48`. The round19 whole-product bound with
multiplier `q^3 h` dominates the new `6h` multiplier because `q>=32`.
Thus the displayed whole product has absolute value less than H, is zero,
and its other factors are positive. Hence `X=2^R`.

As `q|X`, necessarily `q=2^a` for a positive integer a. Now (I), with d=0,
gives `q^6 | 3 ebar`; cancel 3 legitimately to obtain `q^6 | ebar`.
Together with `q^6 | ebar-q^4s`, this gives `q^2|s`. The inherited
projection also gives integral kappa, and the remaining carrier then gives
`h|B` exactly as before.

### Rejected premature divisibility

For `q=3`, `v=27`, `m=2`, the new ebar is congruent to 243 modulo 729.
Thus `q^6 | ebar` fails, although `q^6 | 3 ebar` holds. The same obstruction
persists for even q divisible by 3 (e.g. q=6). This is not a counterexample
to the complete equation: these data have not satisfied its projection.
It identifies exactly why proof order matters.

## 4. Signed bootstrap is simpler

Because k>=2, the correction `vk(k^2-4)/6` is nonnegative. Therefore

    ebar <= k-R-1 < b,
    rho=ebar/q^6 < |b|/q^6.

The retained sign-free bounds `gy<L/2`, `L>0`, and `|b|/q^6<L/2`
now prove `B>=0` directly, including negative R. In contrast to the
incoming rank-cubic correction, no exceptional cases `R<=-4` and `R=0`
need to be controlled. No sign of ebar or rho is assumed.

## 5. One valid positive lift: a cofinal seed

The canonical source data have `q=2^a`, so (I) gives integral rho at the
correct index. However rho is generally negative and the incoming
`rho>=0` completeness sentence must not be reused.

All of `rho`, `kappa`, and `sigma` are determined by the outer source data
before choosing the strong Pell seed. Take a positive multiple of the
finite Pell matrix period modulo `c^2 tau` and increase that multiple until

    g=tau f0 > kappa+sigma+max(0,-rho).

This is possible because the fundamental positive Pell unit has trace
larger than 2, so `f0` grows without bound on period multiples. Set
`i=I0/(c^2 tau)>0`, retain the doubled pair, and invoke the unchanged
auxiliary-completeness theorem for a positive unshifted T. Then

    n = gy+(1+hL)t+rho-kappa-sigma > 0

since `y>=1` and `t>=0`. This constructs every coordinate as a positive
integer. It is not an inverse shear on arbitrary positive tuples.

## Verdict

No obstruction remains in the new arithmetic mechanism after the two
explicit changes above: delayed denominator recovery and a signed positive
lift (the cofinal seed here, or the direct bound in the supplement). Literal DAG cost, all coefficient payloads, complete leading forms,
and packaging should be checked separately by the producer-independent
finite checker. The inherited mathematical calibration boundary remains
unchanged.

## Supplement: enlargement is optional; a direct positive bound

The cofinal construction above is sound, but the ordinary seed already
suffices. At the canonical first index, `k>=R+1`; this follows from
`psi_a(m)>=m` for `a>=1` and `m=(R+1)/2`. Thus

    |rho| <= [k-R-1 + v k(k^2-4)/6]/q^6
           < [k+v k^3/6]/q^6
           < v k^3/3,

where the last step uses `v k^2>6` and `q^6>=1`.
For every allowed `i>=1`,

    g^2=E(1+Delta i^2 c^4 E)>Delta c^4 E^2,
    g>sqrt(Delta)c^2 E>c^2 v^2 k^2>v k^3.

Here `E=1+v(v+1)k^2>v^2 k^2`, `c>k`, and `v>=1`.
Therefore `|rho|<g/3`. Also `sqrt(Delta)>A-1=Y(X+1)>X` and
`cE>4`, so `g>4Xc`. Since the canonical projection and scaling give
`kappa<Xc` and `sigma<=Y<Xc`,

    kappa+sigma+|rho| < g/2+g/3 < g.

Consequently the same formula for n is positive for **every** seed allowed
by the retained period construction; no additional cofinal selection is
needed. This stronger elementary argument may replace the enlarged-seed
paragraph if desired. Neither argument assumes rho nonnegative.
