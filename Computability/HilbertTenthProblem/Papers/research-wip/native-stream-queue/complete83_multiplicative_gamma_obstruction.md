# The current multiplicative-gamma83 chart has empty positive slices

The historical [multiplicative-gamma86 obstruction](complete75_multiplicative_gamma86_obstruction.md) already proves that sharing the input projection product by replacing an additive main quotient with a product destroys completeness. This packet transfers that specific rejected construction to the **current complete84 source**, including its first root, asymmetric scale, auxiliary quotient, scaled strong factor, and final subtraction of Delta. It emits the complete **83=47M+36A** graph with **18 positive witnesses** and exact degree **188**. It has **no positive zeros on any inherited valid fixed compiler slice**, including at accepted inputs.

This is not a new universal bound or a new empty-slice phenomenon. The new record closes the current literal source case and gives a monic projection-polynomial proof using only the weaker native lower bound `R>=3q+1`. It neither alters nor settles the separate independent-gamma83 candidate.

## 1. The full paid source and its maps

The [fresh helper](complete83_multiplicative_gamma_obstruction.py) reads [complete84](complete84_scaled_strong_output.json) as pinned data. Delete its private addition

```
gamma_sum=rho+sigma.
```

Move the existing input producer `modulus_multiple=rho*a4m5` before the main-root consumer and replace that consumer by

```
gam=sigma*modulus_multiple.
```

No operation is charged for moving a row. Every other producer and all seven finalizer rows are literal parent rows. Both main and input roots now reuse the same paid `rho*H`, where `H=a4m5`. There are 41M+35A producer operations and 6M+1A finalizer operations. All 83 gates and all 25 supplied ports, comprising 18 witnesses, x, and six fixed numeral ports, are live. The [receipt](complete83_multiplicative_gamma_obstruction.json) saves the entire array and interface.

Write sigma for the new positive supplied multiplicative quotient. Over every commutative ring,

```
P83(sigma)=P84(sigma_old=rho*(sigma-1)).                  (1)
```

Indeed `rho+rho*(sigma-1)=rho*sigma`; after multiplying by H, every retained row agrees inductively. Equivalently, the graph is the independent-gamma83 polynomial with its independent gamma set to `rho*sigma`. This second map is positive for every positive supplied tuple. It does not require that independent-gamma83 correctly recognize the intended language; only its already established local native consequences will be used.

At sigma=1, the inverse in (1) has sigma_old=0. Thus (1) is not an unconditional map into the parent's strictly positive domain. That boundary is included in the proof below. Nor is there a completeness map from all positive parent zeros: it would require the divisibility refuted here.

## 2. Exact degree on every fixed compiler slice

Use `a=R12`, `c=R10a`, `X=wn2`, and `Gamma=rho*sigma`. Mathematical Pell parameter `A_P=a+2` is distinct from the literal register `A`, which contains `Delta=(a+1)(a+3)=a^2+H`. The main root is

```
D=X+a*c+Gamma*H.
```

The exact norm identity is

```
D^2-Delta*c^2=(X+Gamma*H)^2+2*a*c*(X+Gamma*H)-H*c^2.    (2)
```

In the actual source, `deg(a)=deg(H)=6`, `deg(c)=5`, `deg(X)=2`, and `deg(Gamma)=2`. The unique degree-19 term in (2) is `2*a*c*Gamma*H`; every other expanded term has degree at most 16. Its leader is `8*a_top^2*c_top*rho*sigma`. All other factors are unchanged. Their exact degrees, in literal factor order, are therefore

```
22, 19, 32, 60, 7, 2, 46.
```

Their product has degree 188; the final subtracted Delta has degree 12. More explicitly, the full leading form is the parent's leading form with `rho+sigma` replaced by `rho*sigma`:

```
32 Q^111 h rho sigma delta^2 i^4 (eta+zeta)^13 w^18 s^31
   * Nt_top * T^2 * f^2,
Q=Bm1*Jrep,
Nt_top=w*(Q-F-Z-alpha-twice_cell_bits*x)-transport_quotient*Q.
```

Putting every witness and x equal to one indeterminate makes its coefficient

```
-2^18*(twice_cell_bits+3)*Bm1^111,
```

which is nonzero on every valid fixed compiler slice. This proves the uniform exact degree, not merely a diagnostic degree. The naive gate recurrence still gives 197. Two complete dense modular diagonal expansions corroborate all seven factor degrees and the displayed coefficient; their small numeral assignments are not asserted to be compiler instances.

## 3. Every hypothetical positive zero forces quotient divisibility

Assume a positive zero at positive ordinary input x on a valid compiler slice. Its positive map to independent-gamma83 permits the local pretyping, norm-sign, normalized rank, and native half-binomial conclusions in [that scout, Sections 2–3](complete83_independent_gamma_scout.md), without invoking its unresolved input-language claim. Those arguments use Gamma only to ensure a positive main root; they do not require Gamma>rho. In particular,

```
q>=16, q>=B=2^d, b<=d, C>=0, -q<W<q,
R>=3q+1, R=3 mod4, X=2^R,
c=psi_(A_P)(R), D=chi_(A_P)(R),
a=Y(X+1), H=4a+3, Delta=A_P^2-1,
2Y=sum_(j=0)^r binom(2r,r+j) X^j, r=(R-1)/2.
```

The seven scaled factors have values `1,1,1,1,1,1,Delta`. The source still computes

```
u=2d*x+b, kappa=u+delta*Delta,
mu=W+a*kappa+rho*H,
C=q-F-Z-alpha-2d*x.
```

Since C is nonnegative and F,Z,alpha are positive, `u<q+b`. Also `b<=d<=log2(q)`, and for q>=16,

```
3<=u<q+b<=q+log2(q)<3q/2<R/2.                         (3)
```

u is odd. The original scale bounds also give `R<a<A_P` and `u<A_P`.

The input root is positive because `mu>-q+a*kappa>0`. Its norm-one classification gives `mu=chi_(A_P)(v)`, `kappa=psi_(A_P)(v)` for v>=1. Let

```
E_A(n)=chi_A(n)-(A-2)psi_A(n).
```

For A>=2, this sequence starts at 1,2, obeys `E_A(n+2)=2A E_A(n+1)-E_A(n)`, and is strictly increasing. Since sigma>=1 and X>W,

```
E_(A_P)(v)=W+rho*H < X+rho*sigma*H=E_(A_P)(R).
```

This inequality is strict even at sigma=1. Thus v<R. The standard discriminant congruence gives `psi_A(v)=v mod Delta` for odd v and `psi_A(v)=A*v mod Delta` for even v. With `0<v<R<A_P-1`, these representatives lie between 0 and Delta. Comparing with `kappa=u mod Delta`, and using `u<A_P`, excludes the even branch and forces v=u.

Define the monic integer projection polynomials in a formal variable z by

```
G_0=G_1=0, G_2=1,
G_(n+2)=z*G_(n+1)-G_n+2^n.                            (4)
```

The Pell recurrence gives the polynomial identity

```
(2z-5)G_n(z)=E_(z/2)(n)-2^n.                         (5)
```

At z=2A_P, its denominator is the actual `H=4A_P-5`. Thus `W=2^u mod H`. Because `-q<W<q`, `2^u<X<a`, and `H=4a+3`, no nonzero H shift of `2^u` lies in that interval. Therefore W=2^u exactly. The roots now force

```
rho=G_u(2A_P),
rho*sigma=G_R(2A_P).                                 (6)
```

This is the required numerical divisibility. No positive additive parent sigma has been assumed in deriving it.

## 4. Polynomial nondivisibility for odd indices

For n>=2, (4) makes G_n monic of degree n-2. Also

```
||G_n||_1 <= 2^n,                                    (7)
```

where the norm sums absolute coefficients: induction uses `2^(n+1)+2^n+2^n=2^(n+2)` in (4).

For every pair of odd integers `3<=u<R`, G_u does not divide G_R in Q[z]. This is the historical separating-negative-root argument, here expressed in the monic variable z and with a discrete difference proof.

For `1<l<2`, put `z=-(l+l^(-1))` and, for odd positive n,

```
F_n=E_(z/2)(n)/2^n
   =C*(l/2)^n-D*(1/(2l))^n,
C=(2l+1)/(l^2-1), D=l*(l+2)/(l^2-1).
```

Then F_1=1, F_3>1, and the odd subsequence tends to zero. Its two-step difference, after division by the positive `(l/2)^n`, has sign determined by

```
-C*(1-(l/2)^2)+D*(1-(1/(2l))^2)*l^(-2n).
```

This expression strictly decreases with n. Thus the odd subsequence first increases and then decreases; after returning to level 1, all later terms are strictly below 1.

For odd u>=5, its limit as l tends to 1 is `(3u-1)/2^u<1`, while its value at l=2 is `5/3-(8/3)*4^(-u)>1`. Continuity supplies l_u in (1,2) with F_u=1. At the corresponding z_u, identity (5) gives `G_u(z_u)=0`; every larger odd R has F_R<1 and hence `G_R(z_u)!=0`. Polynomial divisibility is impossible.

For u=3, use `G_3=z+2` and

```
G_R(-2)=(2^R-3R+1)/9>0, R>=5 odd.
```

This covers all required odd indices. It uses no numerical root search or irreducibility assumption.

## 5. The quantitative integer-evaluation obstruction

Polynomial nondivisibility alone is insufficient. Let `D0=u-2`, `L=2^u`, and `B0=L+2`. Divide every G_n by the monic G_u in Z[z], obtaining remainders r_n of degree below D0. The coefficient norm of multiplication by z followed by reduction is at most L: the only exceptional basis vector reduces the monomial `z^D0` to the negative lower part of G_u, whose coefficient norm is below L by (7).

Reducing (4) therefore gives

```
||r_(n+2)||_1 <= L||r_(n+1)||_1+||r_n||_1+2^n,
||r_R||_1 <= B0^(R-2).                               (8)
```

The second inequality follows by induction from `r_2=1` and `||r_3||_1<=L+2`: after dividing the induction step by `B0^(n-2)`, it is enough that `L*B0+1+4<=B0^2`, which holds. By Section 4, r_R is a nonzero integer polynomial.

For any positive integer Z satisfying

```
Z>L+B0^(R-2),                                       (9)
```

the leading integer coefficient of r_R dominates its lower coefficients, so r_R(Z) is nonzero. Furthermore,

```
|r_R(Z)| <= B0^(R-2)*Z^(D0-1),
G_u(Z) >= Z^(D0-1)*(Z-L) > |r_R(Z)| >0.             (10)
```

For a constant remainder, nonvanishing is immediate and the same bound applies. Since monic division gives `G_R=Q*G_u+r_R` with integer Q, (10) excludes `G_u(Z)|G_R(Z)`.

The current native parameter satisfies (9) by a wide strict margin. The leading tail term gives `2Y>=X^r`; hence, for `Z=2A_P`,

```
Z=2Y(X+1)+4 > X^(r+1)=2^[R(R+1)/2].                 (11)
```

From (3), integer u obeys `u< R/2`, so `u+1<=(R+1)/2`. Since `B0<2^(u+1)` and R>=5,

```
L+B0^(R-2)
 <2*B0^(R-2)
 <2^[1+(u+1)(R-2)]
 <=2^[R(R+1)/2-R]
 <2^[R(R+1)/2]
 <Z.                                                (12)
```

Thus (10) contradicts (6). Every hypothetical positive zero gives (6), including the sigma=1 boundary. The current chart has no positive zeros on any valid fixed compiler slice.

## 6. Evidence, provenance, and remaining scope

The helper authenticates ten source/proof files as inert bytes, including the historical multiplicative-gamma86 trio. It executes no predecessor source or verifier. The historical note supplies the original empty-slice phenomenon and negative-root method; the present 83-row source and monic bound are not described as a new independent phenomenon.

Fresh checks include literal parent-row reconstruction, private consumer checks, all-row/free-port liveness, the complete finalizer, 48 full all-value assignments (16 rational, 16 signed, and 16 with sigma=1), and 3,984 retained-register comparisons. The private polynomial identity and unchanged descendants establish the all-ring map; finite evaluations are supplementary.

The helper independently constructs 63 projection identities using the explicit binomial formula for `psi_(z/2)(n)`, checks 62 monic degree/coefficient bounds, and verifies 124 exact nonzero monic remainders and their large-integer evaluation bounds. Eleven further small half-binomial formula evaluations test the native dominance estimate and numerical nondivisibility. They are arithmetic diagnostics, not full compiler histories or positive zeros. No positive compiler zero is claimed or materialized; the theorem says none exist for this chart.

The complete source has exact degree 188 by Section 2, not by extrapolating the two dense diagnostic expansions. No lower bound for other circuits or coordinate charts follows. The established universal84 representation and unresolved independent-gamma83 source are unchanged.

The helper's `PINS` and saved receipt record the exact SHA-256 values. The immediate current parent is PY `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737`, JSON `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`, MD `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. The historical obstruction is PY `58078beb773b23f311292feba17651dbb87bc42d2fa70b0cfd8354baa68276f9`, JSON `58dbeee464988bb02a532df6b237d4544415d9451fd440f64c33ef1424939710`, MD `1800d2c85b5fe895f348d7bdf9fcaf0a8860f93b2d3625a399c587d3e7982986`.

Run the bounded helper with `--root ABS_WIP --expect ABS_JSON`, or use `--output FILE` to emit its deterministic receipt. It uses explicit exceptions and recursive type equality under normal and optimized Python. No maintained arbitrary-input API is claimed.

Fresh normal and optimized (`python3 -O`) exact receipt replays from working directory `/` both passed after the final source and receipt were generated.
