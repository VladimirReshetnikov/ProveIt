# Symbolic current-port zero after freeing `q-F`

An independently reviewed external construction analyzes a second tempting
64-gate coordinate elimination that replaces positive `F` by positive `u=q-F`,
then removes the `q-F` subtraction. The construction below gives that
different candidate a positive symbolic zero at the current fixed port
integers with `u>q`, so the direct inverse `F=q-u` is negative. The enormous
witness is not expanded or numerically evaluated. This does not determine
whether the maintained 65-gate equation has another zero, or disprove bare
zero-existence equivalence by itself.

The 64-row [graph](graph.json) is the current graph with the `qF` row removed,
its uses replaced by the input `u`, and the input `F` renamed to `u`. It has
37 products, 16 additions and 11 subtractions; all inputs and rows are live.
Its output agrees with the old graph under the integer substitution `F=q-u`.
Two hundred modular graph comparisons are controls for the literal binding.

## Current-port scalar construction

Write `beta=2^B-1`, `B=94517`, `q=beta+1`, `lo=MC`, `hi=MF-beta`, and
set `J=1`. The current port bytes satisfy `lo mod4=2`, `hi mod8=4`,
`popcount(lo)+popcount(hi)=B`, and the usual positive scalar boxes. Put

```
G0=q*(hi-1)+lo+1,   G=G0+q³,
R=G*(q²-1)+lo+q*MF,   N=(R-1)/2.
```

The checker verifies `R=3 (mod 4)`, `popcount(R)=3B+2`, and
`popcount(N)=3B+1`. For the population identity, the bit at position `B`
of `G0` is 1, and

```
R=q^5+(G0-q)*q²+(q²-1).
```

The displayed three binary regions do not overlap, and subtracting `q`
removes exactly that one set bit. The rank has bit length 472586.

Let `w=2^(R-B)` symbolically and `M=K+w`. Its residue modulo
`beta=2^B-1` is `Mbar=(K+2^e) mod beta`, with checked `e=27269`.
The checker finds `gcd(Mbar+1,beta)=1`. Define

```
L=floor(G/q)+1,       U=floor((G-1)/beta),
u0=(Mbar*G+1)*inverse(Mbar+1) mod beta,
u=the least integer >=L congruent to u0 (mod beta),
alpha=G-beta*u,       C=u-alpha,
z=(M*C+u-1)/beta.
```

The exact finite check verifies `L<=u<=U`, `u>q`, and `alpha,C>0`.
The integer `u` has bit length 189035 and minimal-unsigned big-endian SHA-256
`7a8968d57505f15ddbf5f18390aea150274df09c959fc36396b274df70b8c959`.
The congruence makes `z` integral, and its
positive numerator makes `z>0`. The graph has

```
beta*u+alpha=G,       C=u-alpha>0,
(K+w)*C+u-z*beta=1.
```

The rank has the stated `R`, while the old inverse gives `F=q-u<0`.
Indeed `G>=q³` exceeds the old scalar upper bound `q²-q-1` when
`F,alpha,C=q-F-alpha` are all positive. Every old positive zero has `Nt=1`
and hence `C>0`, so no old positive zero with the same `q,R`
exists. An arbitrary positive `F,alpha` assignment need not have `C>0`.

## Symbolic remaining coordinates

Set `X=2^R`, `Y` to the binomial-head integer from
`../current14-carrier64-pell-floor/`, and `s=Y/q³`. The population check
gives `v2(Y)=3B`, so `s` is a positive integer. The general construction
proved and independently reviewed in `../current14-carrier64-toy-full-zero/`
then applies with this `q,R,X,Y`: take first and main Pell indices
`(R+1)/2` and `R`; choose `eta,zeta,n,gamma` from their coefficients; take
the `c`-th main-unit power for `f,i`; and take the `R`-th auxiliary-unit
power for `y,T`. The proof there uses only `R=3 (mod4)`, the floor
estimates, the stated congruences and scalar positivity. It yields all norm
factors equal to 1, except the unnormalized strong factor `Delta`; hence the
64-row output is zero. None of those enormous integers is expanded here.

## Scope and reproduction

This is a warning about the free-`u` candidate, not a result about the earlier
free-`C` candidate or the 65-gate equation. In particular it gives no result
on the latter's consistency status or on existential equivalence via some
other witness. The checker pins the maintained source, verifies the current
compressed/raw port hashes and finite modular solve, checks liveness and 200
small modular substitutions, and writes no Lean theorem.
The independent external review is in
`../../reviews/current14-carrier64-free-qminusf-zero-independent/`.

```sh
python3 -I -S -B research/current14-carrier64-free-qminusf-zero/check.py
```
