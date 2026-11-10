# Symbolic current-port zero after freeing k and c

An independently reviewed external construction shows that replacing the two
positive inputs `eta,zeta` by independent positive inputs `c,k` removes the
two additions `k=eta+zeta` and `c=kY+eta`, leaving a 63-gate graph. The
construction below gives this *different* candidate a positive symbolic zero
at the actual current ports. It does not give a zero of the maintained graph
or decide unrestricted zero-existence equivalence.

The literal [graph](graph.json) removes those two rows and renames the two
inputs. It retains `kY=k*Y`, all other rows, and the same integer-leaf metric.
The operation split is 37 products, 14 additions and 12 subtractions; all
inputs and rows are live. Under the integer substitution
`eta=c-Y*k`, `zeta=k-eta`, its output equals the maintained graph; 200 modular
full-graph comparisons are additional controls. Those recovered coordinates
need not be positive.

## Current-port witness

Reuse exactly the scalar fixed point from the independently reviewed
`../current14-carrier63-free-y-zero/`: `J=1`, `C=17`, `e=88042`,

```
q=beta+1=2^B, B=94517,
F=17*(K+2^e) mod beta, alpha=q-F-17,
R=[beta*(q-F)+alpha]*(q²-1)+MC+q*MF,
w=2^(R-B), z=1+((K+w)*17-F)/beta.
```

The fixed checker verifies `F,alpha,z>0`, integral `z`, transport 1,
`R=3 (mod4)`, and `(R-B) mod B=e`. The huge `w` and `z` are specified
symbolically. Now take **s=1**, so `X=2^R`, `Y=q³`, `E=XY`, `m=EY`,
`a=E+Y`, `H=4a+3`, `Delta=a²+H`, and let `j=(R+1)/2`. Define independent
positive candidate inputs

```
k=2*psi_(2m+1)(j),       c=psi_(a+2)(R).
```

Set `tau=chi_(2m+1)(j)`, `D=chi_(a+2)(R)`,
`n=(tau-k+R)/E`, and `gamma=(D-X-a*c)/H`. The independently reviewed Pell
identities in `../current14-carrier64-toy-full-zero/` show `n,gamma>0` are
integers and the first and main factors are 1. The same c-th main-unit power
and R-th auxiliary-unit power from that packet give positive integral
`f,i,T,y` and make the strong and auxiliary normalized factors 1. The
candidate output is therefore zero. Unlike the maintained graph, this
construction does not require `Y*k<c<(Y+1)*k`.

In fact the direct inverse fails with `zeta<0`. Write `N=(R-1)/2`. The
elementary Pell bounds in `../current14-carrier64-growth-window/` give
`c>Y*k` by more than `k` whenever
`(X/6)^N>2*(Y+1)`: use `c>=(XY)^(2N)` and
`k<=2*(6XY²)^N`. Here `R>3B`, so `X=2^R>Y=q³`; also `N>=2` and
`X>=144`. Therefore `(X/6)^N>=X²/36>=4X>4Y>=2(Y+1)`, and hence
`c>(Y+1)k`. Recovering `eta=c-Yk` and `zeta=k-eta` gives `zeta<0`.

The finite rank has `popcount(R)=283450`. A maintained positive zero at the
same `q,R` would have, by the reviewed Pell floor,
`v2(Y)=popcount((R-1)/2)-1=283448`; its own `Y=s*q³` instead has
`v2(Y)>=3B=283551`. Thus no maintained positive zero shares this `q,R`.
This is not a proof that the maintained equation has no other zero.

The checker pins the maintained graph and the reviewed free-Y/toy receipts,
authenticates all four port payloads, checks the finite scalar/valuation
facts, and performs 200 modular graph substitutions. It does not expand the
symbolic Pell witnesses, invoke Lean, or interpret the PDF bytes.
The independent external review is in
`../../reviews/current14-carrier63-free-kc-zero-independent/`.

```sh
python3 -I -S -B research/current14-carrier63-free-kc-zero/check.py
```
