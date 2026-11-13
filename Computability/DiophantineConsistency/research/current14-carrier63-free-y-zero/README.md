# Symbolic current-port zero after freeing Y

An independently reviewed external construction shows that replacing `Y=s*q³`
by an independent positive input `Y` removes two multiplications, giving a
63-gate graph. The construction below specifies a positive symbolic zero at
the actual current port integers for which `q³` does not divide `Y`. Thus
the direct inverse `s=Y/q³` fails. The enormous witness is not expanded or
numerically evaluated; this does not settle whether the maintained 65-gate
equation has some other zero, or bare zero-existence equivalence.

The literal [graph](graph.json) removes the `q3=q²*q` and `Y=s*q3` rows,
renames the positive input `s` to `Y`, and leaves all other rows unchanged.
It has 35 products, 16 additions and 12 subtractions; every row and input
is live. The checker compares the graph under `Y=s*q³` at 200 modular
assignments. These controls do not by themselves prove the symbolic zero.

## Fixed scalar coordinates

Use the actual symbolic ports, `B=94517`, `beta=2^B-1`, and define

```
J=1, q=beta+1, C=17, e=88042,
Mbar=(K+2^e) mod beta,  F=(17*Mbar) mod beta,
alpha=q-F-17,  G=beta*(q-F)+alpha,
R=G*(q²-1)+MC+q*MF,  N=(R-1)/2,
w=2^(R-B),  M=K+w,  z=1+(M*C-F)/beta.
```

The finite checker verifies `F,alpha>0`, `q-F-alpha=C`, `R>=2B`,
`R=3 (mod 4)`, `(R-B) mod B=e`, and `Mbar*C=F (mod beta)`. Hence `z` is
a positive integer and the transport factor is 1. The integer `F` has bit
length 88047 and minimal-unsigned big-endian SHA-256
`0eeb04ceb2c8b15d0a958d94180819cb60a7f022a0487c6c9b3fed2cf22e4b60`.
The full `w` is specified symbolically, not constructed.

## The free Y and Pell coordinates

Set `X=2^R`, and define the positive integer

```
Y=(1/2)*sum_{i=0}^N binom(2N,i)*X^(N-i),
E=XY, m=EY, a=E+Y, H=4a+3, Delta=a²+H.
```

The exact finite rank has `popcount(R)=283450`, so the reviewed central
binomial identity gives

```
v2(Y)=popcount((R-1)/2)-1=283448 < 3B=283551=v2(q³).
```

Consequently `q³` does not divide `Y`. The independently reviewed symbolic
Pell/Chebyshev construction in `../current14-carrier64-toy-full-zero/`
applies to this `X,Y,R`: its first and main Pell indices are `(R+1)/2`
and `R`; the binomial floor estimates give positive `eta,zeta`; the main
projection gives positive `gamma`; the c-th main-unit power gives `f,i`;
and the R-th auxiliary-unit power gives positive integral `y,T`.
The construction requires `R=3 (mod4)`, which is checked here. With the
displayed scalar transport, all normalized factors are 1 and the literal
63-row output is zero. No full enormous coordinate is materialized.

Any positive zero of the maintained equation with this same `q,R` would,
by the reviewed rank-window Pell floor, have the same forced `Y` and hence
would contradict its own `Y=s*q³` with positive integer `s`. This only
excludes an old zero with these same `q,R`; it does not exclude another old
zero or decide consistency.

## Reproduction and boundaries

The checker pins the current graph and reviewed floor/toy receipts,
authenticates all four raw and compressed current port payloads, verifies the
finite scalar/rank arithmetic and 200 modular graph substitutions. It does
not expand the full symbolic Pell witness or invoke Lean. The free-`Y` graph
is not the maintained PDF; no external PDF-byte or new native-proof binding
is asserted.
The independent external review is in
`../../reviews/current14-carrier63-free-y-zero-independent/`.

```sh
python3 -I -S -B research/current14-carrier63-free-y-zero/check.py
```
