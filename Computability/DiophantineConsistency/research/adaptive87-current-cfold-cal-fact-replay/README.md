# Fact-level replay of current 88/28 Cal

The written Cal conclusion `X≥q²` follows in the **standard integers**, using the existing fact-level Pell theorems cited below, from Cal's stated positive inputs, port inequalities, `C>0`, `Y=q³s` with `s>0`, and its four displayed norm equations. The proof does not require the old first-coordinate zero, a sign for `Bt`, or a guard variable. This is a mathematical replay of existing theorem statements, not a new Lean proof, provider replay, all-model transfer, or iPRA endpoint. The current-port inequalities and graph bytes are inherited from the pinned earlier finite receipt.

## Same valuation, orientation and early index

Use the candidate's exact notation:

```
b=J*beta, q=b+1, C=q−F−alpha, Y=q³s, E=XY, m=XY²,
k=eta+zeta, ell=m*k, c=eta+Yk, a=Y(X+1), H=4a+3,
U=Yq², R=(alpha+b(q−F))(q²−1)+J(MC+qMF).
```

All listed input witnesses are positive, and `beta≥46`, `K0≥0`, `0<MC<beta`, `0<MF<2beta`. Thus `q≥47`; `C>0` implies `F+alpha<q` and `R>0`. In Cal, the first norm and the positive `tau` are already assumptions, and `Y=q³s` is already supplied. The following orientation and congruence use the *main* norm and these facts; they do not additionally require a first graph residual.

The actual main expression is

```
Dstar=U(X+a*c)+H(U*gamma+E*q+R+1−k).
```

Since `c>Yk`, `U*a*c>q²Y²ak>Hk` for `q≥3`, `Y≥1`, `a≥2`. Every other term is nonnegative, so `Dstar>0`. From `Dstar²=U²(1+Delta*c²)` with `U>0`, integer square-divisibility gives `Dstar=U*d` for a positive integer d satisfying `d²=1+Delta*c²`. The signed carrier balance is

```
U(d−X−a*c−H*gamma)=H(E*q+R+1−k).                    (1)
```

Because `U=q⁵s`, `E*q` is divisible by q⁴ and `H=3+4q³s(X+1)`. Every common prime of H and q is 3; if 3 divides q, `H≡3 (mod 9)`. Hence `gcd(H,q⁵)=gcd(3,q)` divides q, so (1) implies `q⁴ | R+1−k`, even if the difference is negative. This adapts the pinned orientation proof directly to Cal's supplied Y-divisibility; that packet derives Y-divisibility separately when starting from an actual first residual.

The exact first norm is `tau²=1+m(m+1)k²`. `ArithmeticPellFirstNorm.positive_parameter_solution m tau k` gives a single index n with

```
tau=xcoord n B,  k=2*ycoord n B,  B=2(m−1)+1.
```

Because `B+1=2m`, `ArithmeticPellCongruences.residue_quotients` at modulus `2m` gives the *same* n and a nonnegative w with `k=2n+4m*w`. Similarly `ArithmeticPellClassification.solution_index a d c` gives a single main index p with `d=xcoord p a` and `c=ycoord p a`.

`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`, applied using exactly `F+alpha<q` and the two mask inequalities, gives `R+q³+q+1≤q⁴`, hence `R+1<q⁴`. Also `q−F≥2` and `alpha≥1` give `alpha+b(q−F)≥2q−1`; consequently

```
R ≥ (2q−1)(q²−1) ≥ q³ ≥ 26,
(2q−1)(q²−1)−q³ = (q−2)(q²+q)+1 ≥ 0.
```

Since `Y=q³s`, `q⁴ | 4m`; combining `k=2n+4m*w` with `q⁴ | R+1−k` gives `(2n) mod q⁴=R+1`.

## Exact-index interface

Apply `P72Exact.indices_ordinary` with its arguments

```
(q, X, Y, k, R, g, c, a, y0, i', f, T, u, n, s, μ, m, η)
 = (q, X, Y, k, R, d, c, a, s, i, f, T, u, n, w, q⁴, p, eta).
```

The two uses of `s` above are deliberately different: the first is Cal's positive quotient `Y/q³`; the theorem's later `s` is the Pell quotient w. The first and main Pell equations, `q≥3`, positive X, s, eta, i and f, rank bound, early modulus and ordinate equations are as above. The strong hypothesis is the same graph residual `I²=Delta(f²−1)` with `I=i*c²`, rewritten by adding Delta; no extra Delta factor belongs in i'.

For its auxiliary hypothesis put `A=f²(Tc)` and `B0=f²R+c`. These are nonnegative and the two requested natural `absdiff`s are exactly `|A−B0|=|V|` and `|A+u−B0|=|V+u|`. The stated signed auxiliary norm therefore supplies the theorem's equality without assuming either V or V+u is positive. The conclusion is

```
13≤n,  n<p,  p=R,  2n=R+1.                         (2)
```

An independent source-interface check by the companion reviewer found the same first/main witness mapping, absdiffs and projection direction. The exact graph-to-model and source/provider bindings are not established by that check.

## Recovering the power

Set `W=4Xqsw`. Since `k=R+1+4m*w` and `Y=q³s`, we have `4m*w=U*W`. Substitution into (1), followed by cancellation of positive `Yq`, gives

```
q(d+H*W)=q(X+a*c+H*gamma)+H*X.                      (3)
```

The checker independently proves this substitution identity as an equality in a free integer polynomial ring. As `H=3+qL`, equation (3) gives `q | 3X`. Since `q≥47` and `X>0`, `3X≥q`, hence `X≥16`.

Let `r=n−1`. From (2), `r≥2`, `R=2r+1`, and the same indexed coordinates satisfy all hypotheses of `ArithmeticPellPowerRecovery.power_bound`: `c=kY+eta`, `k=eta+zeta`, `zeta>0`, `c=ycoord R (Y(X+1))`, and `k=2*ycoord (r+1) B`. It gives `2^R<Y` in the standard naturals.

`ArithmeticPellPowerRecovery.projection_quotient a R`, using the *same* d and c, gives `d=2^R+a*c+H*z` for a nonnegative z. Multiply (3) by `L=(H−3)/q` and reduce modulo H; this yields `H | 3(d−X−a*c)`, hence `H | 3(2^R−X)`. No cancellation of 3 or coprimality with H is assumed. Both `3X` and `3*2^R` lie in `[0,H)`: `X<a`, while `2^R<Y≤a`, and `H=4a+3`. Equality of these residues gives `X=2^R`. Finally `R≥q³≥q` and `q≥47` imply `2^R≥2^q≥q²`; the latter follows by induction from `2^4=4²`.

Thus the stated Cal conclusion holds from the four norm hypotheses and port bounds, subject to the cited arithmetic theorems. This does not itself construct or check an IΣ₁-model graph adapter, the unelaborated Lean source composition, a coherent provider closure, or an internal iPRA proof. The fixed-byte/Lean-port and display bindings remain separate.

## Reproduction and scope

`python3 -I -S -B research/adaptive87-current-cfold-cal-fact-replay/check.py` reproduces `receipt.json`. It pins and checks the actual graph's complete 88-row wiring and source theorem-interface markers, and verifies the carrier and q⁴-divisibility polynomial identities exactly. These finite checks do not verify the universal theorem applications, quotient/exponent behavior in models, or Lean elaboration; no Lean/build/staging is run.
