# A symbolic full zero for the q²-scale graph

Replace `Y := q³ s` in the 76Y graph by `Y := q² s` and omit the unused `q3` gate. The result has 75 live operations. At the explicit natural ports `(beta,K0,MC,MF)=(2,2,181803,0)`, the modified graph has a **full positive zero with `Y=18`, hence `q³ ∤ Y`**. Its witnesses are finite integers specified exactly below. The largest of them are far too large to expand: the main Pell coefficient already has roughly 1.31 million bits, while the strong witness is exponentially larger. The [checker](check.py) uses bounded, exact dyadic and modular integer arithmetic and does not expand these coordinates.

This proves that the simple reverse coordinate map requiring `Y=q³ s'` fails on every zero with this displayed tuple. It does **not** show that the original 76Y graph has no other zero at these ports, or settle existence equivalence, the special compact44 ports, an iPRA endpoint, or a global minimum. The construction and proof below are external mathematics, not a Lean theorem.

## Exact witness specification

For an integer `d`, use `(x,y)^e_d` for powers with multiplication `(x,y)(u,v)=(xu+d yv, xv+yu)` and identity `(1,0)`. Put

```
q=3; Y=18; X=3; U=324; a=72; n=74; H=291; D=5475; P=972
j=109930; m=181843
(t,k)=(2P+1,2)^j_(P(P+1))
(g,c)=(n,1)^m_D
eta=c−18k; zeta=19k−c
A=U(g−X−a c)/H; gamma=(k−1+A−m)/U
(f,L)=(g,c)^c_D; I=D L; i=I/c²
(x,y)=(I,1)^m_(I²−1); V=x/I
Q=(c+V)/f²; T=(m+Q)/c.
```

All displayed divisions are exact and all witness values are positive, as proved below. In the modified graph's original input order, the 14 positive inputs are

```
(J,F,alpha,z,f,i,T,s,w,t,eta,zeta,y,gamma)
= (1,1,1,1,f,i,T,2,1,t,eta,zeta,y,gamma).
```

The exact ports above give `R=40+MC=m`. The transport residual is `(K0+w)(q−F−alpha)−F−z(q−1)=0`.

## Bounded checks for the first and main norms

The first Pell power gives `t²−P(P+1)k²=1`, so with `ell=P k` the first graph factor is `A0=t²−ell(ell+k)=1`. The main Pell power gives `g²−D c²=1`.

The checker proves `18k<c<19k` by exact outward-rounded 256-bit dyadic comparisons. In particular `eta,zeta>0`, `eta+zeta=k`, and the graph expression `kY+eta` is exactly `c`. It does not rely on floating point or on expanding `c` or `k`. The comparison uses

```
alpha = n+sqrt(D);   beta = 2P+1+2sqrt(P(P+1)),
c/k = (alpha^m/beta^j) sqrt(P(P+1)/D)
      * (1−alpha^(−2m))/(1−beta^(−2j)).
```

Both bases exceed 2 and both exponents exceed 100, so each subtracted inverse power is below `2^−200`; the dyadic inequalities include that correction. Integer square roots give lower/upper dyadic bounds for the radicals; each product and binary power rounds outward. All mantissas stay at most 256 bits after multiplication, and comparisons use their separate binary exponents.

The checker independently computes `(g,c)≡(131,88) (mod H)`. Thus `g−X−ac≡194 (mod 291)`. Since `gcd(U,H)=3`, the definition of `A` is integral, and `A≡216 (mod U)`. Since `P=XU`, the first Pell recurrence gives `k≡2j≡188 (mod U)`. Finally `m≡79 (mod U)`, so `(k−1+A−m)` is divisible by `U`. Its quotient `gamma` is positive: `k≥2j>m`, and `A>0` because `g>(n−1)c`, `n=a+2` and `c>X`.

With `R=m`, the main carrier gap is `U gamma−k+R+1=A`, so `Dstar=U(X+ac)+HA=Ug`; hence `M=0`. The checker also records `c≡67 (mod U)` and `gcd(c,U)=1`, although the construction above needs only the stated rank congruence.

## Strong and auxiliary factors

The coefficient `L` in `(g+c√D)^c` is divisible by `c²`: the linear term in the binomial expansion has coefficient `c²g^(c−1)`, and higher terms contain at least two factors of `c`. Thus `i=D L/c²` is a positive integer and the graph's strong index `i c²` equals `I`. Multiplicativity of the norm gives `f²−D L²=1`, hence `I²=D(f²−1)` and `W=0`.

In the auxiliary Pell power, the real coefficient `x=T_m(I)` is divisible by `I` because `m` is odd; `V=x/I` and `y` are positive. The norm identity gives

```
I² V² − (I²−1)y² = 1,
```

so using `W=0` the graph's auxiliary factor is `Na=1`.

It remains to justify `Q,T` and bind this `V` to the graph's expression. Let `U_r` denote the second-kind Chebyshev polynomial. Because `I²=D(f²−1)`, we have `I²≡−D=1−n² (mod f²)`. The odd Chebyshev recurrences then give

```
T_m(I)/I ≡ (−1)^((m−1)/2) U_(m−1)(n) ≡ −c (mod f²),
```

where the final sign uses `m≡3 (mod 4)` and the definition of `(g,c)`. Hence `Q=(c+V)/f²` is a positive integer.

Also `c² | I` and `f²≡1 (mod c)`. For odd `m`, the constant term of the polynomial `T_m(X)/X` is `(−1)^((m−1)/2)m`; thus `V≡−m (mod c)`. From `f² Q=c+V` we obtain `Q≡−m (mod c)`, so `T=(m+Q)/c` is a positive integer. Since `R=m`, this gives `cT−R=Q` and therefore the graph's actual auxiliary expression is

```
f²(cT−R)−c = f² Q−c = V.
```

The modified graph consequently has `A0=Na=1` and `M=W=Lt=0`; its sum-of-squares output is exactly zero.

Run from any directory:

```
python3 -I -S -B path/to/p64-qcube75-q2-symbolic-full-zero/check.py
```

The frozen `result.json` records the finite checks and checker hash. These checks validate the bounded arithmetic premises; the universal symbolic argument is the proof above and requires separate review.
