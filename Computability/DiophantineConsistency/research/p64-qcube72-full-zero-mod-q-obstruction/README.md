# A full 72-gate zero failing the carrier congruence

There is a **full positive zero** of the checked 72-gate free-main graph at
explicit natural ports for which `h+k−R−1` is not divisible even by `q`,
and hence not by `U`. Thus the full graph equations alone do not imply the
obvious pointwise inverse to the 76Y carrier coordinate. The ports here are
`(beta,K0,MC,MF)=(2,1,4020579+c,0)`, where `c` is the enormous but explicit
integer below. This is **not** a fixed-compact44 result, a claim that 76Y lacks
another zero at these ports, or a disproof of existential equivalence. The
construction is external symbolic mathematics, not a Lean theorem.

## Exact witness

For integer `d`, write `(x,y)^e_d` for powers with multiplication
`(x,y)(u,v)=(xu+d yv,xv+yu)`. Define

```
q=3; Y=27; X=6; U=729; a=189; n=191; H=759; D=36480; P=4374
j=2446738; m=4020619
(t,k)=(2P+1,2)^j_(P(P+1))
(g,c)=(n,1)^m_D
eta=c−27k; zeta=28k−c
A=U(g−X−a c)/H
(f,L)=(g,c)^c_D; I=D L; i=I/c²
(x,y)=(I,1)^m_(I²−1); V=x/I
Q=(c+V)/f²; T0=(m+Q)/c.
```

The 72 graph inputs, in its original order, are

```
(J,F,alpha,z,f,i,T,s,w,t,eta,zeta,y,h)
= (1,1,1,1,f,i,T0+1,1,2,t,eta,zeta,y,A).
```

All values are finite positive integers. Neither the full main Pell
coordinates nor the vastly larger strong and auxiliary witnesses are
expanded. Their exact definitions determine them unambiguously.

## Proof of the zero and failed inverse

The exact numerical premises come from the independently checked bounded
Pell-pair intervals and modular matrices in the
[free-f² review](../../reviews/p64-free-fsquare75-symbolic-full-zero-independent/README.md):
`27k<c<28k`, `A≡486`, `k≡428`, `m≡184`, and `c≡115 (mod 729)`.
In particular `eta,zeta>0`, `eta+zeta=k`, and `c=27k+eta`. The first and
main Pell norms give `A0=1` and `g²=D c²+1`. The modular main-root check
shows `H | U(g−X−ac)`, so `A` is an integer; it is positive because
`g>(n−1)c>X+ac`. The 72 carrier is `U(X+ac)+H A=U g`, hence `M=0`.

In the strong power, the coefficient `L` is divisible by `c²`: the linear
binomial term has coefficient `c² g^(c−1)` and every later term has at least
two factors of `c`. Therefore `i=D L/c²` is a positive integer. Its norm
gives `f²−D L²=1`, hence `I=i c²=D L` and `W=0`.

The odd auxiliary Pell exponent makes its first coefficient divisible by `I`;
its norm gives `I² V²−(I²−1)y²=1`. Since `I²=D(f²−1)`, modulo `f²` the odd
Chebyshev recurrence gives
`V≡(−1)^((m−1)/2) U_(m−1)(n)=−c` because `m≡3 (mod 4)`. Thus
`Q=(c+V)/f²` is a positive integer. Also `c² | I`, so the constant term of
`T_m(x)/x` gives `V≡−m (mod c)`. As `f²≡1 (mod c)`, this implies
`Q≡−m (mod c)`, making `T0=(m+Q)/c` a positive integer.

At the displayed ports the graph has `R=40+MC=m+c`. With `T=T0+1`,
`cT−R=cT0−m=Q`; its auxiliary expression is `f²Q−c=V`, and the auxiliary
norm therefore gives `Na=1`. Transport is
`(1+2)(3−1−1)−1−1(3−1)=0`. Consequently `A0=Na=1` and `M=W=Lt=0`, so the
full sum-of-squares output is zero.

For the inverse, `U=q^6=729` and the checked residues give

```
h+k−R−1 = A+k−m−c−1 ≡ 486+428−184−115−1 ≡ 614 (mod 729).
```

In particular the expression is `2 (mod 3)`, while any old carrier would
require `U gamma=h+k−R−1`. The full equations therefore do not force this
congruence at arbitrary ports. A different witness or normalization may still
establish an existential implication; compact44 has different fixed ports.

[`check.py`](check.py) pins both actual graph files and the independent
numerical-premise checker, reruns that bounded checker, independently checks
`c mod 729` by matrix powering and the displayed residue, and performs 100
small full-graph comparisons of the transformation `MC→MC+c, T→T+1` with
`J=1`. These finite comparisons are controls only; the exact symbolic argument
above supplies the full zero. Run it with `python3 -I -S -B check.py`.
