# Independent review of the equal-rank first-index obstruction

**PASS in its stated external scope.** The [construction](../../research/p64-qcube72-equal-rank-first-index-obstruction/README.md)
gives a full positive zero at non-compact natural ports, with actual main Pell
index `m=R=19259`. Its old carrier residue is 292 modulo 729 and the first
index `j=11720` satisfies `2j−R−1≡49 (mod 243)`, where `243=729/gcd(729,759)`.
Thus neither required congruence follows from the complete 72 equations and
`m=R` alone. Here `MC=19219>beta=2` and `R+1>q⁴`, so the compact mask and
rank-window hypotheses fail. No fixed-compact44 obstruction, failure of an
existential 76Y witness, or Lean theorem is asserted.

The separate `check.py` computes the two ordinary Pell pairs exactly using a
left-to-right powering algorithm, verifies both norms, `27k<c<28k`, the
positive integral free carrier and both residues, and pins the graph and
author's result. It also evaluates the complete 72-row graph for the
symbolically specified witnesses modulo two primes. Those modular controls
are not a proof of the integer zero or of the exact divisions; the following
symbolic argument supplies those claims.

For `(f,L)=(g,c)^c_D`, the binomial expansion has linear coefficient
`c²g^(c−1)` and all remaining terms contain at least two factors of `c`, so
`c² | L`; thus `i=DL/c²` is a positive integer and the Pell norm gives
`I²=D(f²−1)` for `I=ic²`. In the auxiliary power `(x,y)=(I,1)^m_(I²−1)`,
oddness of `m` gives `I | x` and `V=x/I>0`. The odd Chebyshev polynomial
identity, applied to `I²≡1−191² (mod f²)`, gives
`V≡(−1)^((m−1)/2)U_(m−1)(191)=−c (mod f²)`, since `m≡3 (mod 4)` and
`c` is the second coordinate of `(191,1)^m_D`. Hence `Q=(c+V)/f²` is a
positive integer. The constant term of `T_m(X)/X` is `−m`, and `c² | I`,
so `V≡−m (mod c)`. The strong norm implies `f²≡1 (mod c)`, hence
`Q≡−m (mod c)` and `T=(m+Q)/c` is a positive integer.

The graph has `R=40+MC=m`, transport zero, and `cT−R=Q`; its auxiliary
expression is `f²Q−c=V`. The first and main Pell norms give `A0=1` and
`M=0`, the strong norm gives `W=0`, and the auxiliary norm gives `Na=1`.
Together with transport these make the complete output zero. Graph rows were
inspected directly; the two modular full-DAG runs are independent controls.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-equal-rank-obstruction-independent/check.py
```
