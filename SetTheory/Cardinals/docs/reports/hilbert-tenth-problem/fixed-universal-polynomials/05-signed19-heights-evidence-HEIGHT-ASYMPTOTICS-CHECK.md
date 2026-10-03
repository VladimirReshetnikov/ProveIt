# Independent height check for the fixed-scale signed19 family

Scope: the two supplied proof/audit files were read as inert text. No upstream
program was executed and no repository was edited. Fix the compiler, ordinary
input, repunit, and chosen prime/scale. All asymptotic constants below may depend
on those fixed choices. The coordinate called `alpha` in the source is fixed;
below `alpha` means the logarithm of the main Pell unit.

Write

- `d = sqrt(Delta)`, `alpha = log(A+d)`, `C = alpha/(2 Delta)`;
- `c = sinh(alpha p)/d`, `m = pc`;
- `q = Delta psi_A(m) = d sinh(alpha m)` (the auxiliary parameter, not the fixed source repunit);
- `S = p+2m`, `beta = arcosh(q)`;
- `y = sinh(S beta)/sinh(beta)`, `U = cosh(S beta)/q`.

The source construction uses integer admissible `p`; these formulae also give a
real extension for every `p >= 1`.

## 1. The actual supplied-coordinate height is eventually y

At every sufficiently large admissible pair `(p,n)`, the nonauxiliary variable
coordinates are `O(c+p+1)`. Indeed `k<c/Y`, `eta,zeta<k`,
`h=(k+p-1)/E`, `tau^2=1+XY^2(XY^2+1)k^2`, `Z,rho=O(p)`, and
`0<sigma<gamma=(chi_A(p)-ac-X)/H=O(c)`. The other nonauxiliary
coordinates, including the supplied `alpha` and `delta`, are fixed.

The source gives `q=i c^2` with positive integer `i`, so `q>=c^2`.
Also `q^2=Delta(f^2-1)`, with `Delta>=3` and `f>=2`, implies `f<q`.
Because `S>=3`,

    y >= psi_q(3) = 4q^2-1 > q >= c^2.

Thus `i<=q<y` and `f<y`. The auxiliary Pell norm yields exactly

    U^2 = y^2 - (y^2-1)/q^2 < y^2,

so `U<y`. Consequently

    j=(U-p)/c < y,
    o=(U+c)/f < (y+c)/2 < y.

Finally `y>=4c^4-1` dominates every `O(c+p+1)` coordinate because
`c` grows exponentially and `p=o(c)`. Therefore the maximum of all nineteen
supplied positive coordinates is exactly `y`, with strict dominance,
for all sufficiently large admissible `p`. This conclusion is uniform over the
permitted choice of `n` at a given `p`.

## 2. Strict monotonicity

The real functions `m(p)`, `q(p)`, and `S(p)` are strictly increasing for
`p>=1`, with `q(1)=Delta>=3` and `S(1)=3`. For `beta>0`, `S>1`,
`sinh(S beta)/sinh(beta)` is strictly increasing in each of `S,beta`.
For the less immediate variable,

    d/d beta log[sinh(S beta)/sinh(beta)]
        = S coth(S beta)-coth(beta) > 0,

because `t coth(t)` is strictly increasing on the positive reals:
its derivative has numerator `sinh(t)cosh(t)-t>0`.
Thus `y(p)` is strictly increasing on `[1,infinity)`, not merely on the
admissible subsequence. After the finite threshold in Section 1, ranking
canonical supplied-coordinate heights is exactly ranking their main indices.

## 3. Precise growth and error

Put `L=log d`. As `p` tends to infinity,

    beta = alpha m + L + O(exp(-2 alpha m)),
    log(2 sinh beta) = alpha m + L + O(exp(-2 alpha m)).

Using the exact hyperbolic formula gives the particularly useful estimate

    log y = (2m+p-1)(alpha m+L)
            + O((2m+p) exp(-2 alpha m)).                    (1)

The error is superexponentially small in `p`. For example, it follows by writing
`q=(d/2)exp(alpha m)(1-exp(-2 alpha m))`, expanding `arcosh(q)`, and using
`log y=S beta-log(2 sinh beta)+log(1-exp(-2S beta))`.

Substitution of

    m = p exp(alpha p)(1-exp(-2 alpha p))/(2d)

in (1) proves

    log y = C p^2 exp(2 alpha p)
            + [p/(2d)] [alpha(p-1)+log Delta] exp(alpha p)
            + O(p^2).                                     (2)

In particular, the proposed leading constant is correct:

    log y ~ [alpha/(2 Delta)] p^2 exp(2 alpha p).

More precisely, set `b=log(Delta)/alpha-1`. Then

    log y / [C p^2 exp(2 alpha p)]
      = 1+d(1+b/p)exp(-alpha p)+O(exp(-2 alpha p)),

and hence

    log log y = 2 alpha p+2 log p+log C
                +d(1+b/p)exp(-alpha p)
                +O(exp(-2 alpha p)).                       (3)

This proves the proposed `O(exp(-alpha p))` error and also identifies its
leading term. All errors here are for fixed parameters, not uniform in
arbitrary compiler/scale choices.

For an optional second exponential correction, with `r=exp(-alpha p)`,
the right side of (1), divided by `C p^2 exp(2 alpha p)`, is exactly

    1+d(1+b/p)r
      +[-2+(Delta log Delta/alpha)(p-1)/p^2]r^2
      -d(1+b/p)r^3+r^4.

The remaining normalized error is superexponentially small. Taking its
logarithm gives the `r^2` coefficient in (3) as

    -2+(Delta log Delta/alpha)(p-1)/p^2
       -(Delta/2)(1+b/p)^2.

## 4. Rigorous inverse-height cutoff

Let `B` tend to infinity, and let `p_B` be the unique real solution of
`y(p_B)=B`. This exists for every sufficiently large `B` by Section 2.
Let `W` denote the positive real Lambert W branch and define

    t_B = (1/alpha) W(sqrt(2 alpha Delta log B)).

This is the exact inverse of the leading model:

    C t_B^2 exp(2 alpha t_B) = log B.

Applying (3), the mean value theorem, and the same analytic error estimates
in a neighborhood of `t_B` gives

    p_B = t_B
          - d(1+b/t_B)exp(-alpha t_B)/(2 alpha+2/t_B)
          + O(exp(-2 alpha t_B)).                          (4)

In particular `p_B=t_B+O(exp(-alpha t_B))`, and eventually `p_B<t_B`.
The error scale can also be written

    exp(-alpha t_B)
      = alpha t_B/sqrt(2 alpha Delta log B)
      = O(log log B/sqrt(log B)).

Consequently exact height truncation is simply `p<=p_B`, beyond a fixed
finite initial exception. If the canonical family has at most one tuple per
integer `p`, replacing `p_B` by `t_B` changes its count by at most one for
all sufficiently large `B`. The construction's full ratio interval indeed
has at most one permitted `n=n0+Lv` for a fixed `p`: successive Pell values
in that progression have logarithmic ratio greater than `L beta0`, whereas
the target interval has width `log((Y+1)/Y)<log 2<L beta0`.

An ordinary expansion of the inverse is

    p_B = [log log B-2 log log log B+log(8 alpha Delta)]/(2 alpha)
          + O(log log log B/log log B).                    (5)

Equation (5) is an inverse-height expansion. It is not by itself a
second-order counting theorem.

## 5. What follows for ranked heights, and what does not

Suppose a specified canonical selection has positive main-index density
`rho`, so its number of indices at most `P` is `rho P+o(P)`. If its indices
are `p_1<p_2<...` and its supplied-coordinate heights are `H_r`, then

    p_r ~ r/rho,
    log log H_r ~ (2 alpha/rho)r,
    H_r = exp(exp((2 alpha/rho+o(1))r)).

Also its height counting function is

    N(B) ~ [rho/(2 alpha)] log log B.

At the actual indices, (3) remains valid with `p=p_r`. But the density
statement alone does not justify replacing `p_r` by `r/rho` in the
exponent of a multiplicative equivalent for `log H_r`; nor does it justify
a counting second term proportional to `log log log B`. Such claims need
additional quantitative discrepancy control for the rotation selection.
