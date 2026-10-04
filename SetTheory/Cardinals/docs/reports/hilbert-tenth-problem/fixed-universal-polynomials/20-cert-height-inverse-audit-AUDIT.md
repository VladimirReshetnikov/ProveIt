# Independent audit: convergent all-orders analytic inverse algorithm

## Verdict and scope

**PASS.** The final `INVERSE_ALL_ORDERS.md`, SHA256
`660a86275102fa00d3b5d15f271f29ad21190c79ad9e8a64a7030fd85ebc6e6a`,
proves the claimed convergent Lagrange-inversion algorithm and explicit tail.
The complex bounds, winding-free definitions, nonvanishing denominator,
simple-root holomorphic dependence, coefficient formula, and Cauchy remainder
are valid uniformly over all three branches and real centers `r0>=100`.

The only requested clarification concerned the endpoint: for the arbitrary
center `r0=100`, the inverse lies slightly below 100 and uses the local real
analytic continuation. Starting instead with an actual `R>=100` yields
`r0>R>=100` and recovers that R in the original range. The final draft states
this distinction explicitly. No inequality or formula needed correction.

This is a separately audited extension of the previously sealed E1–E7 packet.
It is a **convergent derivative-algorithm inverse with a computable geometric
tail**, not a claim that all exponential sectors have been sorted into a
canonical transseries. It does not give a smooth ordinary-input asymptotic
across the power-of-five radix jumps.

## 1. Holomorphic definitions and winding

On `|r-r0|<=1/4`, the branch-affine p,L,y satisfy `p0>=66`, `y0>=32`,
`|p|<r0`, and their p/y slopes are positive and below one. The stated bounds
`|d|<2q0` and `|a|<q0^2`, where `q0=2^(-p0)`, follow with ample margin.
The series branches of `ln(1+d)` and g therefore define Phi holomorphically.
The draft then defines `ell_A=L ln2+Phi` directly; it does not take a
principal logarithm of a potentially winding large quantity.

The identity `u=exp(-2p ell_A)` and the rational expression
`b=16u^2/(1-u)^4` are exact analytic continuations of the real quantities.
The successive bounds on u and b validate the Taylor branches in
`ell_S=2p ell_A-ln2+2ln(1-u)+g(b)`. The last conjugate variable is defined
as `v=exp(-2r ell_S)`, again using the specified logarithm itself. Thus
repeated winding of S does not create an unnoticed branch jump. All
logarithms used inside correction functions are evaluated in their small
Taylor disks.

Every inequality is strict on the compact closed r-disk. The holomorphic
functions are constructed in this order, so their definitions are not
circular. Continuity and compactness then give a neighborhood of the disk's
closure on which all relevant Taylor branches and denominators remain valid.

## 2. Uniform disk estimates

The estimates `|Phi|<5q0`, `5r0*q0<1`, and `22r0^2*q0<1` are correct.
For the last two, the values at 100 are already tiny and their logarithmic
derivatives are negative thereafter because `p0'>=2/3`.

Writing `h=r-r0`, `z0=r0+epsilon`, the quadratic bound follows from

    Re((z0+h)^2)>=z0^2-2z0|h|-|h|^2
                 >=r0^2-(5/2)r0+7/16.

Multiplication by `alpha*lambda>=2/3` is valid because the lower bound is
positive. It gives `Re(pL)>=(3/5)r0^2`; the error p*Phi is less than one.
Hence `Re(p ell_A)>(1/2)r0^2 ln2`, establishing

    |u|<2^(-r0^2)<=q0^4,
    |b|<32q0^8<q0^4.

The stated bound `|Q|<11r0*q0` for the correction in ell_S also holds:
its dominant part is below `10r0*q0`, while the remaining logarithm/g
terms total less than `5q0^4`.

For the cubic, Taylor expansion of `r(r+epsilon)^2` about r0 has exactly
the three coefficient bounds printed in the draft. Their total on
`|h|<=1/4` is less than `r0^2`. Consequently

    Re(r pL)>=(2/3)r0(r0-1)^2-r0^2>=(3/5)r0^3.

The Q error in `r ell_S` has modulus below one, since
`|r|<2r0` and `|Q|<11r0*q0`. This proves
`Re(r ell_S)>r0^3 ln2` and then `|v|<q0^4`.

For E, the leading numerator term is below `10r0^2*q0`; all other terms
total less than `(6r0+3)q0^4<r0^2*q0`. Division by ln2 gives the claimed
`|E|<18r0^2*q0`. There is no sign assumption about complex correction terms.

The divided cubic difference is identically

    D(r0+h;r0)=N'(r0)+(1/2)N''(r0)h+gamma*h^2.

Using `N'>3r0^2`, `N''<12r0`, and `gamma<2` gives
`|D|>3r0^2-(3/2)r0-1/8>2r0^2`. In particular D has no zero on the
closed disk. Therefore the holomorphic quotient f obeys the stronger
`|f|<9q0`, hence the stated `|f|<epsilon0=16q0<1/8`.

## 3. Unique holomorphic root and its convergent series

Set `rho=1/(8epsilon0)>1`. For every complex `|t|<=rho`, on the r-shift
boundary `|h|=1/4`,

    |t f(r0+h)|<1/8<|h|.

Rouche's theorem therefore counts exactly one zero of `h+t f(r0+h)`
inside the h-disk, counting multiplicity. The zero must have multiplicity
one. The analytic implicit-function theorem gives a local holomorphic
root in t at every such parameter. Uniqueness makes these local roots
agree on overlaps, producing one holomorphic h(t) on a neighborhood of
the entire closed parameter disk. This also justifies using its full
boundary circle in Cauchy's estimate; a mere pointwise collection of
unrelated local branches would not suffice, but uniqueness supplies the
necessary gluing here.

The standard Lagrange formula for `h=-t f(r0+h)` gives exactly

    h(t)=sum_(n>=1) [(-t)^n/n!]
             (d/dr)^(n-1)[f(r)^n] at r0.

There is no missing derivative or factorial. It initially identifies the
Taylor series at t=0; the proved holomorphy gives convergence at least
through `|t|<=rho`, and in particular at t=1.

Since `|h(t)|<1/4` on `|t|=rho`, its nth coefficient has modulus at most
`(1/4)rho^(-n)`. Summing the geometric tail after K terms yields exactly

    (1/4)*rho^(-K-1)/(1-rho^(-1)), K>=0.

Thus L9 is an explicit valid tail, rather than a formal convergence claim.
For example the n>=2 contribution is bounded uniformly by
`4096q0^2/(1-128q0)`, so its stated `O(q0^2)` consequence follows.

## 4. Identification with the desired real inverse

At t=1, multiplication by D transforms the fixed-point equation into
`N(r0+h)+E(r0+h)=N(r0)`, because h*D is the exact cubic difference.
On the local positive real continuation this is precisely the inverse
log-height equation. Conjugation symmetry and uniqueness make h(1) real.

When the target comes from an actual or interpolated `R>=100`, the
previously audited estimate `0<r0-R<2d<1/4` places that R inside this
unique-root disk, so the analytic algorithm recovers it. The arbitrary
center-100 statement instead invokes the explicitly noted continuation
below 100. No chart interpretation is assigned to noninteger ranks.

The first term is `-E(r0)/N'(r0)` and retains every forward scale.
Keeping its leading `2^(-p0)` sector recovers the earlier inverse
correction. The higher terms are ordered by the artificial parameter t;
this does not itself sort the nested real exponential scales into a
canonical transseries.

## 5. Independent evidence and source boundary

The newly authored `check_inverse.py` passed normal and optimized Python
with byte-identical receipts and 26,373 active checks. It executed no
upstream program or saved graph and materialized no integer witness tuple.
The evidence includes:

* 2,409 exact rational branch/center cases checking the affine, quadratic,
  cubic, derivative, and denominator margins
* 864 complex samples on three radii, all three branches, and centers
  `100,100.5,143,250`, using the specified winding-free logarithms and
  arbitrary-precision conjugate exponentials
* Nine real inverse cases with derivative-defined Lagrange coefficients
  through order five, checked against independently iterated roots and
  every explicit L9 tail from K=0 through K=5
* 36 sampled roots on the large artificial-parameter circle `|t|=rho`,
  verifying disk containment, residuals, and simplicity

The largest sampled `|f|/epsilon0` was below 0.033704, and the largest
sampled L9 error-to-bound ratio was below 0.01503. Numerical checks are
**corroborative, not interval-certified**. All uniform and all-orders
conclusions follow from the proof review above, not from those samples.
The independent source binding and file manifest accompany this verdict.
