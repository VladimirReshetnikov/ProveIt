# Exact certificate specification

## Arithmetic and conventions

Let zeta = exp(2*pi*i/3). A pair `(a,b)` represents `a+b*zeta`.

```text
(a,b)*(c,d) = (a*c-b*d, a*d+b*c-b*d)
conjugate(a,b) = (a-b, -b)
```

All data are integers. The witness has schema version 1.

The eight independent line variables are `t[2*d]=g[d,0]` and
`t[2*d+1]=g[d,1]`, with `g[d,2]=1/(t[2*d]*t[2*d+1])`.
The exponent of a class's third variable is `-e[2*d]-e[2*d+1]`.

The basis is the lexicographically sorted set of 241 exponents consisting of
zero, each line exponent and its negative, and the positive and negative sums
and differences of exponents from distinct parallel classes. See equation
(5.1) of the article. The verifier reconstructs this basis.

## Matrices

```text
Q = (QA + QB*zeta) / 2592000000
K =  KA + KB*zeta
L = (LA + LB*zeta) / 1000000
```

`Q` and `L` have order 241; `K` has 241 rows and 28 columns. `L` is lower
triangular. With `m(t)=(t^u)` in basis order, the verifier establishes

```text
Q = Q*
QK = 0
rank(K) = 28
m(t)* Q m(t) = 153 - Kcal(g)
Q + K K* - L L* >= mu I,
```

where the star denotes conjugate transpose and `Kcal` is the scalar Laurent
polynomial, distinct from the matrix `K`.

The exact diagonal-bound margin is

```text
mu = 646878666855648000000 / 2592000000000000000000
   = 6738319446413 / 27000000000000
   > 1/5.
```

The coefficient at exponent `v-u` in the Gram expression is accumulated from
`Q[u,v]`. Reversing this convention without also conjugating would give the
wrong identity.

## Why the matrix witness proves nonnegativity

Put `N=range(K)` and `H=Q+K K*`. The triangular factor and diagonal-dominance
check give `H >= mu I`. For `w=w0+w1` with `w0 in N` and `w1 perpendicular to N`,
Hermitian symmetry and `QK=0` give

```text
w* Q w = w1* Q w1 = w1* H w1 >= mu ||w1||^2.
```

Hence `Q` is positive semidefinite and its kernel is exactly `N`. It is not
necessary to trust a numerical eigenvalue or compute a square root of `Q`.
The rank of `Q` is 213.

For the exact diagonal-bound check, all entries of `H-L L*` are placed over
the denominator `D*R^2`. A lower off-diagonal numerator `a+b*zeta` has absolute
value at most `|a|+|b|`. Its upper conjugate has the distinct bound
`|a-b|+|b|`. The checker uses the appropriate bound in each row. The minimum
real diagonal numerator minus that row's off-diagonal bounds is the numerator
of the displayed margin.

## Equality information

Each column of `K` is an actual coefficient vector of `m` restricted to one
of the four equality tori. These coefficient vectors are reconstructed from
the family table, not accepted from the file as an unexplained nullspace.
Their independence is checked modulo 7, under the homomorphism `zeta -> 2`.
Since `2^2+2+1=0 (mod 7)`, a nonzero 28-by-28 minor after reduction implies a
nonzero minor over Q(zeta).

A Laurent polynomial supported in the monomial basis and vanishing on all
four families has a coefficient row annihilating `K`. The separators in
article equation (6.1) therefore vanish whenever the energy is maximal. This
proves exhaustiveness of the four families, after a check of the remaining
81 constant-class points.

## Trust boundary

The electronic witness was discovered using numerical and symbolic search,
but that search is not part of the proof check. The proof is independently
replayable from the displayed definitions, the integer matrices, and the
standard-library verifier. The package does not provide a Lean certification
or a claim that the numerical discovery path is unique or necessary.

A successful hash comparison identifies the data; it is not a mathematical
proof. A successful verifier execution checks the stated finite identities.
The surrounding analytical implications are proved in the article.
