# The two fixed charts already minimize height under integer translations

For each of the two exactly specified quartics in the observed fixed58
checkpoint, the minimum coefficient height over all constant integer
translations is **128446**. The current chart attains that bound. Further
centering can change lower-degree terms or their count, but cannot lower
the coefficient height. This ordinary statement concerns the two pinned
polynomials; the separate native/refutation calibration and complete replay
remain separate proof obligations.

## Exact inputs and coefficient certificate

Use the plain and weighted expanded_polynomial.json files under
research/round16-common-name-centering/data/. They have316 and315
unrestricted integer coordinates respectively. Coordinates10,11,12 have
the literal names crt.encoded.a, crt.encoded.b, crt.encoded.c in both.
After collecting every integer coefficient, each polynomial contains

    [x_10^2*x_11*x_12] P = 128446.

This term has total degree4. Complete per-degree collection gives:

| Degree | Plain terms | Plain height | Weighted terms | Weighted height |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 2674 | 1 | 2674 |
| 1 | 112 | 2116 | 112 | 2116 |
| 2 | 806 | 10806 | 805 | 10806 |
| 3 | 1389 | 32588 | 1391 | 32590 |
| 4 | 3429 | 128446 | 3434 | 128446 |

Thus both have exact degree4 and height128446. The complete supports
have5737 and5743 terms. SOURCE_PINS gives full file hashes, all independent
degree census values and the outside observed34-file source inventory.
That observation record preserves the existing data and receipts; it is
not a final accepted-endpoint manifest. No new polynomial or tuple has
been generated for this note.

## Proof of the height bound

Let P in Z[x_0,...,x_(n-1)] have total degree d, and let delta be any
fixed integer vector. For a monomial x^alpha with |alpha|<=d, the only
term of degree |alpha| in (z+delta)^alpha is z^alpha, with coefficient1.
Every term using at least one constant delta factor has smaller degree.
Consequently the complete degree-d homogeneous component satisfies

    (P(z+delta))_d = P_d(z).

This is an identity over all coefficients, for every delta, rather than
a finite set of sampled translations. The degree4 coefficient128446
above is therefore unchanged in every translated polynomial. Its height
is at least128446. Taking delta=0 attains the actual current height, so

    min_(delta in Z^n) H(P(z+delta)) = 128446.

The same argument applies to rational or real constant translations if
height means maximum absolute monomial coefficient. Here only integer
translations preserve the intended integer domain bijectively.

## A different research direction: an integral shear

A change of linear coordinates can change the leading form. For example,
on the three named coordinates one may specify

    x_10=z_10-z_11, x_11=z_11, x_12=z_12,
    x_i=z_i for every other i.

This integer matrix has determinant1 and inverse

    z_10=x_10+x_11, z_11=x_11, z_12=x_12,
    z_i=x_i for every other i.

It gives a bijection of Z^n. Substitution in every quadratic residual
preserves its degree bound; substituting in the full sum of squares gives
the same zero set under that bijection. The full quartic degree remains4
because the inverse matrix makes substitution injective and its leading
form cannot vanish. The number of live coordinates must be checked again;
an invertible change may expose a previously hidden free direction.

To compose a resulting witness map, first apply this matrix to recover
the current centered tuple, then its fixed58 translation to the accepted
raw tuple, then the existing complete raw Horn/monic/source maps. Every
coordinate and residual must participate in the finite verification.

This explicit example only identifies an eligible class of changes. No
sheared polynomial, new height/term count, improvement or page endpoint
is claimed. Any implementation needs a separately frozen preparation,
complete static reviews and execution release. The maintained complete
compact66 PDF/TeX and paused Lean work remain unchanged.
