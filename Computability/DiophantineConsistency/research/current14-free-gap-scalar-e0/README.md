# An actual-port scalar fixed point with exponent residue zero

This is **scalar-only progress** toward testing the 64-gate free-Pell-gap
candidate. It does not construct the first/main Pell coordinates, the
relaxed auxiliary factor, or a full zero, and it assumes no maintained zero.
It is not a Lean or PDF result.

Authenticate the maintained graph's complete four port payloads. Write
`beta=2^B−1`, with `B=94517`, and set

```
J=1, q=beta+1, C=342757,
F=C*(K+1) mod beta, alpha=q−F−C,
gap=beta*(q−F)+alpha,
R=gap*(q²−1)+MC+q*MF, w=2^(R−B),
z=1+((K+w)*C−F)/beta.
```

The checker proves `F,alpha,C>0`, `R>=2B`, `R=3 mod 4`, and `R=0 mod B`.
Thus `w=1 mod beta` and the numerator defining z is divisible by beta.
Moreover `w>=q>F` and `C>=1`, so z is positive. The literal transport
factor is exactly 1. The rank has 378068 bits and SHA-256
`7d8959244948cd8209556620c04c3112abaced0c03e527bef7bdb730c161d7f0`;
F has 47290 bits and SHA-256
`be5fe0dc508767d0c161c4f799c4594c206ff8b22b42c07b24597676c0ac2f37`.
The exponentiation defining w is symbolic and is not expanded.

The familiar canonical completion would take `X=2^R`, `N=(R−1)/2` and

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j).
```

The previously reviewed central-binomial valuation is
`v2(Y)=popcount(N)−1=282615`, strictly below `3B=283551`. Consequently
this particular canonical Y is not divisible by `q³`, so it cannot provide
the required positive integer s. This rules out that **particular** Pell
completion only. Other first/main indices, X choices and scalar assignments
remain open; the computation does not show an actual-port candidate zero or
exclude one.

```
python3 -I -S -B research/current14-free-gap-scalar-e0/check.py > /tmp/free-gap-scalar-e0.json
cmp /tmp/free-gap-scalar-e0.json research/current14-free-gap-scalar-e0/result.json
```

Independent external review is recorded in
`../../reviews/current14-free-gap-scalar-e0-independent/`.
