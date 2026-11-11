# Proposed sign-free calibration for the 87/26 probe

This packet proposes an **external standard-integer proof** that every
positive zero of `../ordinary14-shifted-guard87-probe/` at the authenticated
compact44 ports has `omega>F`. Combined with that packet's coordinate maps,
this would give positive-zero existence equivalence with the 88/26 guarded
parent. The proposed replay is submitted for independent review. It is not a
Lean proof about the modified graph, a new iPRA theorem, a fresh provider or
object-ancestry replay, a PDF binding, or an unconditional claim about
arbitrary ports.

The key point to check is that the original literal-zero theorems are
**not applied directly** to the probe. Their fact-level arithmetic and
proof steps are replayed from the probe's four vanishing residuals, the guard,
and positivity. The inherited theorem statements below are in Lean for an
`ORingStructure V` whose underlying structure models `IΣ₁`; here the
application is only to the ordinary natural numbers. Port bytes and the
referenced current source files are pinned by the checker; it does not build
or validate their provider closures.

## Input facts, port bounds and rank window

All 14 inputs are strictly positive. Let

```
b=J*beta, q=b+1, C=q−F−alpha, E=X*Y, m=E*Y,
k=eta+zeta, c=eta+Y*k, a=E+Y, H=3+4*a,
Delta=(a+2)²−1, U=Y*q², M=q³*b,
G=b*(q−F)+alpha, R=G*(q²−1)+J*(MC+q*MF).
```

The actual ports satisfy `beta>=46`, `0<MC<beta`,
`0<MF<2*beta`, and `K0>=0`. The probe guard is

```
b*omega=C*(X+K0*q)−F.
```

Its left side is positive, so `C>0` and `F+alpha<q`; this uses **no sign
assumption on Bt**. The source theorem `scalar_rank_window` in
`ArithmeticAdaptiveRankWindow2011.lean` assumes precisely positive
`beta,J,F,alpha`, `MC<beta`, `MF<2*beta`, `q=beta*J+1` and
`F+alpha<q`. Its conclusion gives

```
24<=R,    R+q³+q+1<=q⁴.                    (2)
```

Moreover `q−F>=2`, so `G>=2q−1`. With nonnegative MC and MF,
`R>=(2q−1)(q²−1)>=q³>=27`; thus the `R>=26` hypothesis below holds.
The checker authenticates these fixed-port bounds but does not execute the
source theorem.

The probe is a sum of five squares. Its first norm gives a positive integer
`tau` with

```
tau²=1+m*(m+1)*k²,    q³|Y.
```

Indeed, `M²|Z²` gives `M|Z`, and the probe's
`Z=M*(ell+k−sigma_prime)+Y*b` then gives `q³|Y`. Write
`Y=q³*y0` with `y0>0`. The main norm similarly gives a positive `d` with
`d²=1+Delta*c²` and `U|Dstar`.

## Main orientation and early congruence without Bt

The signed main expression is

```
Dstar=U*(X+a*c)+H*(U*gamma+E*q+R+1−k).
```

It is positive: `c>Y*k`, `U=Y*q²`, and `q²*Y²*a>H` for `q>=3` and
`Y>=q³`, so `U*a*c>H*k`; the remaining terms are nonnegative. Therefore
`Dstar=U*d`, not the negative branch. It follows that

```
H*(E*q+R+1−k) = U*(d−X−a*c−H*gamma).
```

Since `U=q⁵*y0`, `E*q` is divisible by `q⁴`, and
`H=3+4*q³*y0*(X+1)`, this yields

```
q⁴ | R+1−k.                                (3)
```

For the cancellation, every prime factor common to `H` and q is 3; if
3 divides q then `v3(H)=1`, so `gcd(H,q⁵)<=3<=q`. Thus q⁵ divisibility
leaves at least q⁴. This is the integer content of
`rank_congruence_from_main` in `FreeJMainOrientation.lean`. Its bundled
`main_oriented` wrapper starts from an original literal zero, but its proof
uses the original first transport to get `F+alpha<q` and `q³|Y`; both are
proved above directly, without recovering the old first coordinate or Bt>0.
The displayed direct orientation is the needed replacement.

Classify the first Pell solution by a positive index n and the main solution
by a positive index p. With `ycoord` as in the source recurrence,

```
k=2*ycoord n (2*(m−1)+1),
c=ycoord p a,
k=2*n+4*m*w    for some w>=0.
```

The last congruence follows from the recurrence modulo `2m`. Since
`q³|Y`, also `q⁴|4m`; combining (2), (3), and the equation for k gives

```
R+1<q⁴,    (2*n) mod q⁴ = R+1.             (4)
```

This is the fact-level content of `FreeJEarlyIndex.early_index_of_facts`,
with modulus **q⁴**, not `XY`. Its first-norm input is the Pell solution
above; no sign or magnitude of the old first-root coordinate is used.

## Exact index theorem: complete hypothesis mapping

`P72Exact.indices_ordinary` in `P72Exact.lean` assumes, in addition to its
model context, the following natural-number data and hypotheses:

```
q>=3, X>0, y0>0, Y=q³*y0,
eta>0, c=eta+Y*k, i_prime>0, f>0, a=X*Y+Y,
R>=26,
k=2*ycoord n (2*(m−1)+1), k=2*n+4*m*w,
R+1<mu, (2*n) mod mu=R+1,
c=ycoord p a, d²=1+Delta*c²,
(i_prime*c²)²+Delta=Delta*f²,
Delta*(f²−1)*|V|²+|V+u|² = 1+Delta*(f²−1)*|V+u|²,
```

where `V=f²*(T*c−R)−c`, `u` is the positive graph input, and
`Delta=3+4*a+a²`. Its conclusion is `13<=n`, `n<p`, `p=R`, and
`2*n=R+1`.

For the probe use `mu=q⁴`; (4) supplies the modulus conditions. All
positive parameters and the first/main Pell data were given above. The
strong residual gives `(i*c²)²=Delta*(f²−1)`; set
`i_prime=i>0` and add Delta to both sides for the displayed strong
hypothesis. The auxiliary residual `Fa=1` is exactly the displayed
absolute-square equation, because its two absdiff terms in the source are
`|V|` and `|V+u|`. No assumption `V>=0` or `V+u>=0` is needed. This
accounts for every explicit argument of `indices_ordinary`; the theorem is
not supplied a parent literal zero or a positive old first coordinate.

## Recovering X and the guard sign

Set `W=4*X*q*y0*w`, so `4*m*w=U*W`. Substitute the exact index equation
`k=R+1+U*W` into the oriented main carrier and cancel positive `Y*q`:

```
q*(d+H*W)=q*(X+a*c+H*gamma)+H*X.           (5)
```

As `H=3+q*D` for an integer D, (5) gives `q|3X`. Since
`q>=beta+1>=47` and `X>0`, this gives `X>=16`.

`ArithmeticPellPowerRecovery.power_bound` assumes exactly `X>=16`, `Y>=1`,
`r>=2`, `c=k*Y+eta`, `k=eta+zeta`, `zeta>0`,
`c=ycoord (2r+1) (Y*(X+1))`, and
`k=2*ycoord (r+1) (2*(X*Y²−1)+1)`; it concludes `2^(2r+1)<Y`.
With `r=n−1`, the exact indices give all of these, and hence `2^R<Y`.

Multiplying (5) by D and reducing modulo H gives
`3*d=3*(X+a*c) (mod H)`. The Pell projection identity used in
`FreeJPowerFinish.lean` gives `d=2^R+a*c (mod H)`. Consequently
`3*X=3*2^R (mod H)`. Both `3X` and `3*2^R` are less than `H=4a+3`, since
`X<a` and `2^R<Y<=a`; therefore `X=2^R`. This is the source's
three-multiplier argument, and does not assume q is coprime to H or q|X.

Because `R>=q³` and `q>=3`, elementary monotonicity gives `X=2^R>=q²`.
The positive inputs and C>0 give `F<=q−2`, so

```
Bt=C*(X+K0*q)−F*q >= q²−(q−2)*q = 2q > 0.
```

Finally the literal guard identity yields `Bt=b*(omega−F)`; since b>0,
`omega>F`. The positive-coordinate comparison in the 87/26 probe then
constructs an 88/26 zero. The other existence direction was already explicit.
The argument uses source theorems as external mathematical inputs and has
not been checked in Lean for this modified graph.

```
python3 -I -S -B research/ordinary14-shifted-guard87-calibration/check.py > /tmp/shifted-calibration.json
cmp /tmp/shifted-calibration.json research/ordinary14-shifted-guard87-calibration/result.json
```

The finite checks pin named source files, verify actual port bounds and
exercise the orientation and gcd estimates. They are not a substitute for
the unbounded theorem applications or an independent provider replay.

Independent mathematical review is recorded in
`../../reviews/ordinary14-shifted-guard87-calibration-math-independent/`.
A separate independent decoder review is recorded in
`../../reviews/ordinary14-shifted-guard87-calibration-decoder-independent/`.
