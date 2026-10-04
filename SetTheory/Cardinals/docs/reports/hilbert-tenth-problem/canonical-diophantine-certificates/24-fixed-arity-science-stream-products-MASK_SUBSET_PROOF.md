# A paid fixed-arity binary mask relation

Own derivation, 4 October 2026. This module is a finite conjunction of explicitly listed arithmetic equations. The number of variables and equations does not depend on the mask length or its value. It does not use a generic MRDP representation, an unexpanded bitwise operation, or an unpaid digit-extraction primitive.

## Interface

Inputs are two nonnegative integers `M` and `X`. The relation `MaskSubset(M,X)` means that every binary 1-position of `X` is a binary 1-position of `M`. Equivalently, `X & M = X`, where this notation describes the intended semantics only and is not part of the arithmetic formula.

All internally quantified variables below are strictly positive. `qPlus`, `oPlus`, and `rPlus` represent the nonnegative integers

    q = qPlus - 1,  o = oPlus - 1,  r = rPlus - 1.

Introduce eight positive outer witnesses

    L, Y, Z, qPlus, oPlus, rPlus, s_c, s_r.

Use the following three explicit power assertions:

    POWER(2, M+1, L)
    POWER(L, X, Y)
    POWER(L+1, M, Z).

Here `POWER(b,e,p)` is the supplied 15-polynomial-equation, 25-positive-witness macro asserting `p=b^e` for `b>=2,e>=0`. Each call receives a fresh disjoint set of its 25 witnesses. Its full equations and proof dependency are in the read-only mathematical source

    /workspace/shared/complete-ant-certificate-recovered-20261004-v2/dependencies/RECODER_PROOF.md, section 5.

No upstream code was executed in deriving or checking this module. The constructive indexed-Pell theorem is the only substantial external mathematical dependency inherited through POWER.

Set `c=2o+1` as an expression, and impose exactly three more equations:

    Z = (q L + c) Y + r
    c + s_c = L
    r + s_r = Y.

No additional bound `X<=M` is needed. In particular, the relation itself rules out `X>M`.

## Domain check for all three power calls

Since `M>=0`, the first power has base 2 and exponent `M+1>=1`, so it yields `L>=2`. The second call therefore has valid base `L>=2` and exponent `X>=0`. The third has valid base `L+1>=3` and exponent `M>=0`. All power outputs are positive, including `Y=1` if `X=0` and `Z=1` if `M=0`.

## Soundness: no fake odd coefficient

The power calls force

    L = 2^(M+1),  Y = L^X,  Z = (1+L)^M.

Every coefficient of `(1+t)^M` is a nonnegative integer at most `2^M`, hence strictly less than `L`. Thus the binomial expansion is literally the carry-free base-`L` expansion

    Z = sum_{j=0}^M binom(M,j) L^j.

The positive slacks give `0<c<L` and `0<=r<Y`. Since `q>=0`, the first equation is the unique Euclidean division decomposition of `Z` with low remainder `r` modulo `Y` and next base-`L` digit `c`. More explicitly, dividing first by `Y` gives

    floor(Z/Y) = q L + c,

and reducing this quotient modulo `L` gives

    c = floor(Z/L^X) mod L.

Consequently `c=binom(M,X)` when `0<=X<=M`, and `c=0` when `X>M`. The latter is impossible because `c=2o+1>=1`. There is no freedom to adjust `q`, `r`, or `c` to fake oddness: their signs and both strict remainder bounds are enforced.

Write the binary expansion `M=sum_j m_j 2^j`, with `m_j` in `{0,1}`. In the polynomial ring over the field of two elements, repeated squaring gives

    (1+t)^M = product_{j:m_j=1} (1+t^(2^j)).

The exponents in the expanded product are distinct subset sums of distinct powers of two. Therefore the coefficient of `t^X` is 1 exactly when the binary 1-positions of `X` form a subset of those of `M`. This is precisely the claimed relation. This elementary proof supplies the required parity fact directly rather than invoking an unexpanded Lucas-theorem oracle.

## Completeness

If the binary support of `X` is contained in that of `M`, then `X<=M`, and the parity identity above says that `c=binom(M,X)` is odd. Set the three power outputs to their actual values. Divide `Z` by `Y` and then its quotient by `L`, obtaining the unique nonnegative `q,r` and the digit `c`. Set `o=(c-1)/2`, `s_c=L-c`, and `s_r=Y-r`. The carry-free coefficient bound and Euclidean remainder bound give both slacks strictly positive. Add 1 to each of `q,o,r` for its positive adapter, and use completeness of each supplied POWER macro. This constructs every required positive witness.

For the smallest valid case `M=X=0`, take `L=2,Y=Z=c=1,q=o=r=0,s_c=s_r=1`. Thus the zero mask and empty support need no exceptional formula or disjunction.

## Exact ledger under the supplied expression-DAG convention

A binary addition/subtraction costs one A, a multiplication costs one M, fixed numerals are free, aliases and equality assertions cost nothing, and expression nodes are not independently quantified. Input ports are not counted as internal witnesses.

The outer arithmetic nodes can be listed explicitly:

1. `M+1` [A]
2. `L+1` [A]
3. `qPlus-1` [A]
4. `oPlus-1` [A]
5. `rPlus-1` [A]
6. `2o` [M]
7. `c=2o+1` [A]
8. `qL` [M]
9. `qL+c` [A]
10. `(qL+c)Y` [M]
11. `(qL+c)Y+r` [A]
12. `c+s_c` [A]
13. `r+s_r` [A].

Thus the outer part uses `3 M + 10 A`, eight positive witnesses, and three equations. The supplied POWER receipt is `31 M + 39 A`, 25 positive witnesses, and 15 equations per call. The complete MaskSubset module consequently uses:

- 3 POWER calls, each explicitly expanded by the same fixed polynomial macro
- 96 M + 127 A = 223 arithmetic operations
- 83 positive internal witnesses
- 48 polynomial equations

These counts do not include input-port adapters. If both inputs are provided as positive ports `MPlus,XPlus`, use `M=MPlus-1,X=XPlus-1` and charge two additional A operations, for 225 operations; those two input ports remain external. If only one port needs this adapter, charge exactly one A. If only literals 1 and 3 are initially free, constructing 2 once costs one A; it can be shared with the surrounding circuit. The POWER macro also uses 4, so if neither 2 nor 4 already exists, create `2=1+1` and `4=3+1` once, at a total of two A for the combined module.

The 48 equations may be combined into one equation by a sum of squared residuals. The generic separate cost is 48 subtractions, 48 multiplications, and 47 additions, namely 143 further operations. No such compression cost is included in 223.

## Relevant stream specializations

If `B=2^b`, `b>=1`, and `R=(B^n-1)/(B-1)` is enforced by paid power and the polynomial equation `(B-1)R=B^n-1`, then `MaskSubset(R,X)` says exactly

    X = sum_{i=0}^{n-1} x_i B^i,  x_i in {0,1}.

For `0<=d<=b` and `D=2^d`, `MaskSubset((D-1)R,X)` says exactly that the base-`B` stream has `n` lanes and each lane belongs to `[0,D)`. All powers in these hypotheses must be produced by paid POWER calls. In the first specialization the mask has one bit per lane; in the second it has exactly the lowest `d` bits per lane, with no overlap because `d<=b`.

More generally, arbitrary finite sparse binary masks can be supplied as nonnegative arithmetic expressions. The MaskSubset formula itself is unchanged.

## Validation scope

`verify_mask_subset.py` is an own, finite arithmetic check of the coefficient extraction, parity equivalence, exact witness equations, and the outer gate receipt. It does not execute the upstream recoder, its DAG generator, or Lean. Finite testing is supplementary; the proofs above establish the all-mask theorem.
