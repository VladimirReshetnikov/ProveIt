# A 72-graph zero with equal main index and rank but missing first-index relation

The 72-operation graph has a positive zero at the explicit natural ports
`(beta,K0,MC,MF)=(2,1,19219,0)` where the main Pell index `m` equals
the graph rank `R`, yet the old carrier congruence fails. In particular,
`h+k−R−1 ≡ 292 (mod 729)` and `2j−R−1 ≡ 49 (mod 243)`, where `j` is
the first Pell index. Thus the full graph equations and `m=R` alone cannot
supply either congruence at arbitrary ports.

This is an external symbolic construction, not a Lean theorem. The chosen
ports do **not** satisfy the compact mask bound `MC<beta`, and their rank also
violates `R+1<q⁴`. It says nothing about the existence of an alternative
76Y witness at these ports, or an existential reverse implication at the
fixed compact44 ports.

## Exact definitions

For integers `d` and `e≥0`, let `(x,y)^e_d` use multiplication
`(x,y)(u,v)=(xu+d yv,xv+yu)`. Put

```
q=3, Y=27, X=6, U=729, a=189, H=759, D=36480, P=4374
m=19259, j=11720, R=19259
(g,c)=(191,1)^m_D
(t,k)=(8749,2)^j_(P(P+1))
eta=c−27k, zeta=28k−c
h=U(g−X−a c)/H
(f,L)=(g,c)^c_D, i=D L/c², I=i c²
(x,y)=(I,1)^m_(I²−1), V=x/I
Q=(c+V)/f², T=(m+Q)/c.
```

All these numbers are finite positive integers. The graph inputs, in original
order, are `(J,F,alpha,z,f,i,T,s,w,t,eta,zeta,y,h)` with
`(J,F,alpha,z,s,w)=(1,1,1,1,1,2)`. The enormous `f,i,T,y` are defined
symbolically and are not expanded by the checker.

## Verification

The two Pell norms and exact inequalities `27k<c<28k` imply positive
`eta,zeta`, `eta+zeta=k`, and `c=27k+eta`. Since the graph's first
root is `ell=P k`, the first norm yields `A0=1`. Also
`g²−D c²=1`. The exact integer computation checks that the displayed
formula for `h` is integral and positive; therefore the free main carrier
is `U(X+a c)+H h=U g` and `M=0`.

The coefficient `L` of the strong power is divisible by `c²`: its linear
binomial term is `c² g^(c−1)` and every higher term has at least two factors
of `c`. Thus `i` is integral and positive. The strong norm gives
`f²−D L²=1`, and hence `I=D L=i c²` and `W=0`.

Because `m` is odd, `x` is divisible by `I`; the auxiliary Pell norm gives
`I²V²−(I²−1)y²=1`. The odd Chebyshev recurrence modulo `f²`, together
with `I²=D(f²−1)` and `m≡3 (mod 4)`, yields
`V≡−U_(m−1)(191)=−c (mod f²)`. Thus `Q` is a positive integer. Since
`c²|I`, the constant term of `T_m(I)/I` gives `V≡−m (mod c)`;
moreover `f²≡1 (mod c)`, so `Q≡−m (mod c)` and `T=(m+Q)/c` is
also a positive integer.

The graph computes `R=40+MC=m`, so `cT−R=Q`, and its auxiliary
expression is `f²Q−c=V`. Since `I²=D(f²−1)`, the auxiliary norm gives
`Na=1`. Transport is `(1+2)(3−1−1)−1−1(3−1)=0`. Thus all four
squared residuals vanish and the graph output is zero. The auxiliary
Chebyshev argument is the same as in the earlier independently reviewed
[full-zero construction](../p64-qcube72-full-zero-mod-q-obstruction/README.md),
with this packet's exact indices and unchanged sign condition `m≡3 (mod 4)`.

The checker evaluates the two 165,000-bit Pell pairs exactly, without
expanding the much larger strong or auxiliary witnesses. It verifies both
Pell norms, all displayed finite size and divisibility claims,
`h mod 729 = 486`, `k mod 729 = 112`, and `R mod 729 = 305`. It also
checks `gcd(729,759)=3`, so `mu=243`, and calculates the first-index
residue. The checker pins the 72 graph and compares independent residual
formulas with its complete gate evaluator on 160 deterministic small cases;
these finite cases are controls, not an evaluation of the symbolic full zero.
Run `python3 -I -S -B check.py`; retained output is [result.json](result.json).
