# A full zero after freeing the X coordinate

Modify the 76Y graph by deleting `X := w*q` and substituting the positive input `w` for `X` in every later gate. The 75-operation graph has a full positive zero at natural ports `(beta,K0,MC,MF)=(2,1,226403,0)` with `q=3` and `w=8`. Thus `q ∤ w`, so the proposed pointwise inverse requiring an old positive coordinate `w_old=w/q` fails on this zero.

There is a direct forward map from an old positive zero: put `w_new=q*w_old` and `z_new=z_old+w_old*C`, where `C=q−F−alpha`; keep the other inputs and ports. The old transport equation forces `C>0`, so the new `z` is positive, and its new transport residual equals the old residual. All other graph expressions agree. This is an external mathematical argument, not a checked Lean theorem.

The constructed zero does **not** show the original 76Y graph has no other zero at these ports. It does not decide positive-zero existence equivalence, special compact44 ports, an iPRA endpoint, or minimality. Its enormous witnesses are specified by finite integer formulas and never expanded.

## Exact witness

For integer `d`, write `(x,y)^e_d` for powers with multiplication `(x,y)(u,v)=(xu+d yv, xv+yu)`. Put

```
q=3; Y=27; X=8; U=729; a=243; n=245; H=975; D=60024; P=5832
j=139466; m=226443
(t,k)=(2P+1,2)^j_(P(P+1))
(g,c)=(n,1)^m_D
eta=c−27k; zeta=28k−c
A=U(g−X−a c)/H; gamma=(k−1+A−m)/U
(f,L)=(g,c)^c_D; I=D L; i=I/c²
(x,y)=(I,1)^m_(I²−1); V=x/I
Q=(c+V)/f²; T=(m+Q)/c.
```

All displayed divisions are exact and the resulting inputs are positive. In the modified graph's 14-input order use

```
(J,F,alpha,z,f,i,T,s,w,t,eta,zeta,y,gamma)
= (1,1,1,4,f,i,T,1,8,t,eta,zeta,y,gamma).
```

Here `R=40+MC=m`, and `(K0+w)(q−F−alpha)−F−z(q−1)=9−1−8=0`. The main Pell coefficient has roughly 2.02 million bits; `f,i,T,y` are vastly larger, but each is a precisely defined finite integer.

## Exact bounded arithmetic

The first Pell norm gives `t²−P(P+1)k²=1`, hence `A0=1`; the main norm gives `g²−D c²=1`. The checker proves **`27k<c<28k`** by exact integer dyadic intervals with 256-bit product mantissas; therefore `eta,zeta>0`, `eta+zeta=k`, and `kY+eta=c`. It never expands `t,k,g,c` or the larger witnesses.

For that comparison it bounds square roots with integer `isqrt` and rounds every dyadic multiplication outward. If `alpha=n+sqrt(D)` and `beta=2P+1+2sqrt(P(P+1))`, then

```
c/k = (alpha^m/beta^j) sqrt(P(P+1)/D)
      * (1−alpha^(−2m))/(1−beta^(−2j)).
```

Both bases exceed 2 and both exponents exceed 100. The inequalities include the conservative `2^−200` correction for both inverse powers. No floating-point arithmetic is used.

The checker also establishes `(g,c)≡(65,249) (mod H)`. Therefore `g−X−a c` is divisible by `H` and `A` is integral with `A≡0 (mod U)`. Since `P=XU`, the first Pell recurrence yields `k≡2j≡454 (mod U)`, while `m≡453 (mod U)`, so `gamma` is integral. The bound `k≥2j>m` and `A>0` give `gamma>0`; for the latter, `g>(n−1)c` and `c>X` suffice.

The new main gap is `U gamma−k+R+1=A`, and `Dstar=U(X+ac)+HA=Ug`. Thus `M=0`.

## Strong and auxiliary factors

The coefficient `L` in `(g+c√D)^c` is divisible by `c²`: the linear term is `c²g^(c−1)`, and all higher terms contain at least two factors of `c`. The norm gives `f²−D L²=1`, so `i=D L/c²>0`, `I=i c²`, and `W=I²−D(f²−1)=0`.

Since `m` is odd, the real coefficient `x=T_m(I)` of the auxiliary Pell power is divisible by `I`; `V=x/I` and `y` are positive. Its norm gives `I² V²−(I²−1)y²=1`, so the graph's `Na=1` once the graph expression for `V` is bound to this value.

Because `I²=D(f²−1)`, modulo `f²` we have `I²≡−D=1−n²`. The odd Chebyshev recurrence yields

```
V=T_m(I)/I ≡ (−1)^((m−1)/2) U_(m−1)(n) ≡ −c  (mod f²),
```

using `m≡3 (mod 4)` and the definition of the main Pell coefficient. Thus `Q=(c+V)/f²` is a positive integer. Also `c² | I`, and the constant term of `T_m(X)/X` gives `V≡−m (mod c)`. Since `f²≡1 (mod c)`, the identity `f²Q=c+V` gives `Q≡−m (mod c)`. Therefore `T=(m+Q)/c` is a positive integer and, with `R=m`, the graph expression is exactly

```
f²(cT−R)−c = f² Q−c = V.
```

Thus the modified graph has `A0=Na=1` and `M=W=Lt=0`; its output is zero. The bounded checker validates the numerical inequalities and residues, while the symbolic argument above supplies the full witness. Neither is a Lean theorem.

Run from any directory:

```
python3 -I -S -B path/to/p64-free-x75-symbolic-full-zero/check.py
```

The deterministic finite-check result and checker hash are frozen in `result.json`.
