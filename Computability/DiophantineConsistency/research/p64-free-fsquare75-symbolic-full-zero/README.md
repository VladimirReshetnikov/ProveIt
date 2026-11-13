# A full zero after freeing the squared-f coordinate

Modify the 76Y graph by deleting `f2 := f*f` and replacing its positive input `f` by an independent positive input `F2` everywhere that `f2` was used. The resulting 75-operation graph has a full positive zero at natural ports `(beta,K0,MC,MF)=(2,1,4020579,0)` with `F2` a nonsquare. The old positive witness maps forward by `F2=f²`, preserving all graph values; the direct pointwise inverse requiring `F2=f²` is impossible at this zero.

This does **not** show that the original 76Y graph has no other zero at these ports, or settle positive-zero existence equivalence, the fixed compact44 ports, an iPRA endpoint or a global minimum. The zero uses finite integers specified exactly below; their huge values are not expanded. The proof is external mathematics, not a Lean theorem.

## Exact witness

For integer `d`, use `(x,y)^e_d` for powers with multiplication `(x,y)(u,v)=(xu+d yv, xv+yu)` and identity `(1,0)`. Put

```
q=3; Y=27; X=6; U=729; a=189; n=191; H=759; D=36480; P=4374
j=2446738; m=4020619
(t,k)=(2P+1,2)^j_(P(P+1))
(g,c)=(n,1)^m_D
eta=c−27k; zeta=28k−c
A=U(g−X−a c)/H; gamma=(k−1+A−m)/U
F2=1+D c⁴; i=D; I=i c²
(x,y)=(I,1)^m_(I²−1); V=x/I
Q=(c+V)/F2; T=(m+Q)/c.
```

All displayed divisions are exact and all inputs are positive. In the modified graph's 14-input order use

```
(J,F,alpha,z,F2,i,T,s,w,t,eta,zeta,y,gamma)
= (1,1,1,1,F2,D,T,1,2,t,eta,zeta,y,gamma).
```

The ports above give `R=40+MC=m`. The transport residual is `(K0+w)(q−F−alpha)−F−z(q−1)=3−1−2=0`. The main Pell coefficient has roughly 34.5 million bits, and the auxiliary witnesses are much larger; these sizes are descriptive, not required for the proof.

## Bounded numerical verification

The first Pell norm gives `t²−P(P+1)k²=1`, hence the graph's first factor `A0=1`; the main norm gives `g²−D c²=1`. The checker proves **`27k<c<28k`** using exact outward dyadic arithmetic with 256-bit product mantissas. Thus `eta,zeta>0`, `eta+zeta=k`, and the graph expression `kY+eta` is `c`.

With `alpha=n+sqrt(D)` and `beta=2P+1+2sqrt(P(P+1))`, the exact ratio is

```
c/k = (alpha^m/beta^j) sqrt(P(P+1)/D)
      * (1−alpha^(−2m))/(1−beta^(−2j)).
```

The checker bounds the square roots with integer `isqrt`, rounds each multiplication outward, and includes a conservative `2^−200` bound on both inverse-power terms. It uses no floating point or expansion of `c` and `k`.

Modular Pell powering gives `(g,c)≡(488,538) (mod H)`, so `g−X−a c≡506 (mod 759)`. Since `gcd(U,H)=3`, `A` is an integer and `A≡486 (mod U)`. The first Pell recurrence gives `k≡2j≡428 (mod U)` because `P=XU`; also `m≡184 (mod U)`. Hence `gamma` is integral. It is positive because `k≥2j>m` and `A>0`; the latter follows from `g>(n−1)c`, `n=a+2`, and `c>X`.

As `R=m`, the main gap is `U gamma−k+R+1=A`, so `Dstar=U(X+ac)+HA=Ug` and `M=0`.

Finally the checker verifies `c≡29 (mod 31)`, giving `F2=1+D c⁴≡13 (mod 31)`. Euler's criterion checks `13^15≡−1 (mod 31)`, so `F2` is not the square of an integer.

## Strong and auxiliary factors

By definition `I=i c²=D c²` and `F2−1=D c⁴`, hence `I²=D(F2−1)` and `W=0`. The auxiliary Pell power has an odd exponent, so its real coefficient `x=T_m(I)` is divisible by `I`; put `V=x/I>0`. Its norm gives `I² V²−(I²−1)y²=1`, so the graph's `Na=1` once its expression for `V` is bound to this value.

Because `I²=D(F2−1)`, modulo `F2` we have `I²≡−D=1−n²`. The odd Chebyshev recurrence yields

```
V=T_m(I)/I ≡ (−1)^((m−1)/2) U_(m−1)(n) ≡ −c  (mod F2),
```

using `m≡3 (mod 4)` and the definition of the main Pell coefficient. Therefore `Q=(c+V)/F2` is a positive integer. Since `c²|I`, the constant term of `T_m(X)/X` gives `V≡−m (mod c)`; and `F2≡1 (mod c)`. From `F2 Q=c+V` it follows that `Q≡−m (mod c)`, so `T=(m+Q)/c` is a positive integer. With `R=m`, the modified graph expression is

```
F2(cT−R)−c = F2 Q−c = V.
```

Thus `A0=Na=1` and `M=W=Lt=0`; the graph output is zero. The bounded checker validates the finite inequalities, residues and nonsquare certificate; the symbolic argument above supplies the full witness.

Run from any directory:

```
python3 -I -S -B path/to/p64-free-fsquare75-symbolic-full-zero/check.py
```

The deterministic bounded-check output and checker hash are frozen in `result.json`.
