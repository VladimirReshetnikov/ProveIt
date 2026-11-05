# A nonsquare first root in the 75-operation free-square graph

Start from the checked 76Y graph and replace the positive first-root witness
`t` by a positive independent `tFirst`, deleting the gate
`first_unscaled_square := t*t`. The first residual becomes
`A0 := tFirst - ell*(ell+k)`; all other rows are unchanged. The resulting
[graph](graph.json) has **14 positive inputs and 75 live operations**: 41
multiplications, 18 additions and 16 subtractions. Its degree is 104 for
nonzero beta: the 76Y leading form, which has degree 104 and contains no
`t`, is unchanged, and replacing `t²` by `tFirst` cannot increase degree.
The exact parent graph hash is pinned in [check.py](check.py). Its association
with the checked Lean provider retains the parent packet's qualifications.

The map from a positive 76Y zero to this graph sends `tFirst` to `t²` and
leaves the other inputs unchanged. The construction below gives a **full
positive zero of the 75-operation graph with nonsquare `tFirst`** at arbitrary
natural ports `(beta,K,MC,MF)=(2,2,159,0)`. Thus the direct inverse at this
witness does not exist. This is an external symbolic integer argument, not a
Lean theorem. It does not show the 76Y graph lacks another zero at these ports,
settle the fixed compact44 ports, prove inequivalence of existence, or provide
an iPRA endpoint. In particular, these ports do not obey `MC<beta`.

## Exact witness

For integers `d`, write `(x,y)^r_d` for the `r`th power under
`(x,y)(u,v)=(xu+d*y*v,x*v+y*u)`. Set

```
q=3, X=3, Y=162, U=Y²=26244, a=(X+1)Y=648,
H=4a+3=2595, D=(a+1)(a+3)=422499, P=XU=78732, m=199,
(g,c)=(650,1)^m_D,
h=U(g-X-a*c)/H,
lo=floor(c/(Y+1))+1,
k=lo+((m+1-h-lo) mod U),
eta=c-Y*k, zeta=(Y+1)*k-c,
gamma=(h+k-m-1)/U,
tFirst=1+P(P+1)k²,
(f,L)=(g,c)^c_D, i=D*L/c², I=i*c²,
(x,y)=(I,1)^m_(I²-1), V=x/I,
Q=(c+V)/f², T=(m+Q)/c.
```

Use witness coordinates `(J,F,alpha,z,f,i,T,s,w,tFirst,eta,zeta,y,gamma)`
with `(J,F,alpha,z,s,w)=(1,1,1,1,6,1)`. Every displayed quotient is a
positive integer. The checker evaluates the finite `g,c,h,k,eta,zeta,gamma`
exactly: `c` has 2,049 bits, the two scale gaps and `gamma` are positive,
all three integer divisions used in this finite core are exact, and
`tFirst ≡ 2 (mod 5)`. Thus `tFirst` is not a square. The symbolically defined
strong and auxiliary witnesses are finite but much too large to expand.

## Symbolic verification

The main Pell norm gives `g²-Dc²=1`. The exact check establishes
`H | U(g-X-a*c)`; its quotient is positive `h`, and the selected `k` makes
`U | h+k-m-1`, with positive `gamma`. Consequently the graph's main
carrier is `U(X+a*c)+H(U*gamma-k+R+1)=U*g`. The transport equation holds:
`(K+w)(q-F-alpha)-F-z(q-1)=3-1-2=0`; the graph rank is `R=40+MC=m`.
Since `ell=P*k`, the new first residual is exactly `A0=1` by definition of
`tFirst`. The main squared residual is zero by the main norm.

In the strong power `(f,L)=(g,c)^c_D`, the linear term of `L` is
`c²*g^(c-1)` and every further term contains at least two factors of `c`.
So `c² | L`, and `i=D*L/c²` is a positive integer. Its norm yields
`I²=D(f²-1)`, so the graph's strong residual is zero.

For the auxiliary power, odd `m` makes `I | x` and `V=x/I>0`. The odd
Chebyshev identity together with `I²≡-D≡1-650² (mod f²)` and
`m≡3 (mod 4)` gives `V≡-U_(m-1)(650)≡-c (mod f²)`. Hence
`Q=(c+V)/f²` is a positive integer. The constant term of `T_m(I)/I` is
`-m`, and `c² | I`, so `V≡-m (mod c)`; moreover `f²≡1 (mod c)`. Thus
`Q≡-m (mod c)`, making `T=(m+Q)/c` a positive integer. The graph has
`c*T-R=Q` and auxiliary expression `f²Q-c=V`. The auxiliary Pell norm then
gives `Na=1`, so the final unit residual and all four squares vanish.

The structural checker pins the parent, checks the one deleted gate and all
75 rows and inputs are live, computes the finite core exactly, and evaluates
the complete modified DAG modulo 1,000,000,007 and 1,000,000,009 using the
symbolic definitions. Those modular runs are controls, not a substitute for
the exact divisibility and Pell argument above. Reproduce with
`python3 -I -S -B check.py`; the recorded output is [result.json](result.json).
The checker rejects optimized Python, which would disable its assertions.
