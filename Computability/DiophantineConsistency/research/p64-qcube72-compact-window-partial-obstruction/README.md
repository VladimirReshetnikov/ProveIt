# A compact-window partial obstruction for the 72 graph

The 72 graph's first, main, strong and transport equations, even together
with the rank window and the same port-size inequalities used for compact44,
do **not** alone force the carrier congruence needed by the direct inverse.
This packet gives an exact symbolic partial assignment with

```
(beta,K0,MC,MF)=(2,1,1,0),  q=3,  R=41,
MC<beta,  MF<2 beta,  R+1=42<q⁴=81,  2R<c,
q ∤ (h+k−R−1).
```

The **auxiliary equation fails** for the displayed choices `T=y=1`; this is
not a 72 zero, an actual compact44-port result, a counterexample to existence
equivalence, or a Lean theorem. It shows that any proof from the compact-like
size bounds must use the auxiliary constraint or additional specific
properties of the compact44 ports.

## Exact assignment

For integer `d`, write `(x,y)^e_d` for powers using multiplication
`(x,y)(u,v)=(xu+d yv,xv+yu)`. Put

```
q=3; Y=27; X=6; U=729; a=189; n=191; H=759; D=36480; P=4374
j=2446738; m=4020619
(t,k)=(2P+1,2)^j_(P(P+1))
(g,c)=(n,1)^m_D
eta=c−27k; zeta=28k−c
A=U(g−X−a c)/H
(f,L)=(g,c)^c_D; i=D L/c².
```

At the ports above take the 14 positive 72 inputs

```
(J,F,alpha,z,f,i,T,s,w,t,eta,zeta,y,h)
= (1,1,1,1,f,i,1,1,2,t,eta,zeta,1,A).
```

The two large Pell powers and the larger strong witness are finite integer
expressions, not decimal expansions. The independent
[free-f² bounded audit](../../reviews/p64-free-fsquare75-symbolic-full-zero-independent/README.md)
certifies `27k<c<28k`, integrality and positivity of `A`, and
`A≡486, k≡428 (mod 729)`. It follows that `eta,zeta>0`, their sum is `k`,
and `c=kY+eta`. The first Pell norm gives `A0=1`; the main Pell norm and
`H A=U(g−X−ac)` give `M=0`. The strong binomial expansion gives `c²|L`, so
`i` is a positive integer, and the strong Pell norm gives `W=0`.

The stated ports give `C=1`, `R=41` and
`Lt=(1+2)−1−(3−1)=0`. Also `k≥2j`, so `c>27k>82=2R` and `c>55`.
Since `A≡0` and `k≡2 (mod 3)`,

```
h+k−R−1 ≡ 0+2−41−1 ≡ 2 (mod 3).
```

For `T=y=1`, `V=f²(c−41)−c`. The positive strong Pell power gives `f≥2`,
so `V≥3c−164>1`; using `W=0`, `Na=1+I²(V²−1)>1`, where `I=i c²`.
Thus the actual output is strictly positive. A different `T,y` might or
might not solve the auxiliary equation; no claim is made either way.

[`check.py`](check.py) authenticates the graph and independent bounded Pell
checker, reruns the latter, checks the small rank/transport/port calculations
and residue, and verifies the numerical lower bound used above. It does not
expand `c`, `f`, or `i`; the exact norm and inequality argument supplies the
partial assignment. Run it with `python3 -I -S -B check.py`.
