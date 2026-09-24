# A 69-operation cyclic Rule 110 certificate with a short mask

A radix-16 affine local rule, a selectively doubled Boolean field, and
a factored transport equality give **69=38M+31A** for an exact cyclic
Rule 110 relation. The system has three supplied positive parameters
`q,P,C`, 23 positive existential unknowns, and 16 equations.

The exact predicate is

    q=16^N, P=16^h, 1<=h<=N,
    C=sum_{i=0}^{N-1} c_i 16^i>0, with each c_i in {0,1},
    c_{i-h-1}=Rule110(c_{i+h},c_i,c_{i-h}) for every i mod N.

It is a complete positive certificate for this predicate. It is not a
raw-input universal certificate and has no marker, target, or halting
interface. Compared with the separate
[radix-128 cyclic certificate](EXPLORATION_RULE110_CYCLIC_CERTIFICATE.md),
the supplied integers use a different numerical radix. The same abstract
cyclic Boolean relation is encoded; equality of the numerical predicates
at unchanged `q,P,C` is not claimed. This relation also differs from the
finite-history endpoint relation.

The [checker](../verification/explore_rule110_cyclic_short_mask.py) and
[receipt](../verification/explore_rule110_cyclic_short_mask.json) include
the complete 69-instruction source and exact polynomial comparisons.
Numerals and equality checks are free; both products and additions or
subtractions count, including the scalar products and power construction.

## 1. A one-bit affine local test

For Boolean `l,c,r,y`, set

    phi(l,c,r,y)=1+l+3c+3r+4y.

The scalar table is

| l c r | Correct y | phi at y=0 | phi at y=1 |
|---|---:|---:|---:|
| 000 | 0 | 1 | 5 |
| 001 | 1 | 4 | 8 |
| 010 | 1 | 4 | 8 |
| 011 | 1 | 7 | 11 |
| 100 | 0 | 2 | 6 |
| 101 | 1 | 5 | 9 |
| 110 | 1 | 5 | 9 |
| 111 | 0 | 8 | 12 |

Consequently `phi AND 4=0` exactly for the Rule 110 output, and every
raw value lies in `[1,12]`. Also every valid output satisfies
`y<=c+r`. Let `B=16` and, once the geometry is decoded, put

    D=q-1, J=D/15, P=B^h.

From the Boolean word `C`, form the cyclic words

    L_i=c_{i+h}, R_i=c_{i-h}, Y_i=c_{i-h-1}.

Their integer values are congruent to `P^(-1)C,PC,BPC` modulo `D`.
Define

    Factual=J+L+3C+3R+4Y,
    K(P)=1+P(3+67P).

Since `PJ==J (mod D)`, multiplication by `P` gives

    P Factual == K(P)C+J  (mod D).                       (1)

There is no intercell carry and

    0<J<=Factual<=12J<D.                                 (2)

Thus, for an already Boolean word in the decoded geometry, the congruence
and `0<F<q` force the exact equality `F=Factual`. This will be applied only
after those word and geometry properties have been proved.

## 2. Positivity of the quotient and the factored local equality

Write the actual nonnegative wrap quotients as

    PL=C+kL D, R=PC-kR D, Y=BPC-kY D,
    PJ=J+align D, where align=(P-1)/15.

Here `0<=kL<P` and `kR,kY>=0`. Equation (1) has the exact quotient

    z=[K(P)C+J-PFactual]/D
      =P(3kR+4kY)-kL-align.                             (3)

For a valid nonzero Rule 110 word, `Y<=C+R<=C+PC`. If `kY=0`, the equality
`Y=BPC` contradicts `BP>1+P`, since `C>0`. Therefore `kY>=1` and

    z>=4P-(P-1)-(P-1)/15=(44P+16)/15>0.                 (4)

This permits one positive quotient unknown, with no signed adapter.
The source does not construct `K` and then multiply it by `C`. Instead,
it uses the identical residual in the factored equality

    P[(3+67P)C-F]+C+J=z(q-1).                            (5)

It has eight operations, `4M+4A`. The intermediate subtraction is a
computed integer register; no positivity is assumed for it in soundness.
For a genuine word it is positive as well: by (5), its product with `P`
is `zD-C-J>0`, since `z>=1` and `C+J<=2J<D`.

## 3. Complete system and ledger

Besides the positive parameters `q,P,C`, supply six positive outer
unknowns

    v,J,align,F,alpha,z

and seventeen positive kernel unknowns

    a,c,d,f,h0,i,j,k,o,r,s,w,tau,eta,zeta,gamma,yaux.

The checker names the outer repunit `Jrep` and quotient `zquot`, and uses
`h,ga,y_aux` for `h0,gamma,yaux`. Construct by counted arithmetic

    C2=C+C, Lambda=q*q, D0=Lambda*q=q^3,
    S=C2+qF, M=(13+4q)J.                                (6)

The six outer equations are

    15J=q-1, Pv=q, 15align=P-1,
    C2+alpha=q,
    P[(3+67P)C-F]+C+J=z(q-1),
    r=(Lambda-S)(Lambda-1)+M.                            (7)

For `X=wD0`, `Yp=sD0`, `Delta=a^2+4a+3`, and `u=jc-(2r+1)`, the ten
fixed-minus kernel equations are

    XYp^2(XYp^2+1)k^2=tau(tau+1),
    c=Yp k+eta, k=eta+zeta, k=r+1+h0 XYp,
    a=Yp(X+1), d=X+ac+gamma(4a+3),
    d^2=Delta c^2+1,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-yaux^2)=1-yaux^2,
    u=of-c.                                             (8)

`D0` is named `n2` in the retained arithmetic schedule. This name does
not assume it is a square before the power-decoding proof. The computed
register `u` may also have either sign in soundness.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry: `q-1,15J,Pv,P-1,15align` | 3 | 2 | 5 |
| Bound, reusing `C2`: `C2+alpha` | 0 | 1 | 1 |
| Factored local equality (5) | 4 | 4 | 8 |
| Powers `Lambda=q*q,D0=Lambda*q` | 2 | 0 | 2 |
| `C2=C+C,S=C2+qF` | 1 | 2 | 3 |
| `M=(13+4q)J` | 2 | 1 | 3 |
| Index: `Lambda-S,Lambda-1`, product, `+M` | 1 | 3 | 4 |
| Outer subtotal | 13 | 13 | 26 |
| Retained fixed-minus kernel | 25 | 18 | 43 |
| **Complete source** | **38** | **31** | **69** |

The local eight-instruction list is `67P`, `3+67P`, its product with `C`,
subtraction of `F`, product with `P`, `C+J`, addition of those two terms,
and `z(q-1)`. Formation of `C2` is charged once and shared with the bound.
Packing, including both powers and `C2`, costs twelve operations. All
source equalities are exact; the checker verifies the usual acyclic
correction in the auxiliary norm by the preceding norm residual.

## 4. Strict field bounds before the kernel

Take any positive solution of the full source. Geometry gives
`q>=P>=16`, and the bound gives `0<C2<q`. No power or Boolean interpretation
has yet been used. By the repunit equation,

    (Lambda-1)-M=J(11q+2)>0.                             (9)

If `S>=Lambda+1`, then the index equation would give
`r<=-(Lambda-1)+M<0`, a contradiction. Thus `S<=Lambda`. Since
`qF<S<=q^2`, we have `F<q`. Both fields now lie strictly below `q`, so

    0<S=C2+qF<Lambda.                                   (10)

In particular the boundary `S=Lambda` is excluded before the kernel;
it cannot conceal a mask exception. Equivalently, its residue modulo
`q` would be the nonzero number `C2`.

The strict positive gap and (9) imply

    r>=Lambda-1+M>q^2-1,
    r<Lambda^2=q^4.                                     (11)

In particular, by integrality `r>=q^2>=256`, and `D0=q^3<r^2`. This
stronger bound avoids any reliance on a separately estimated mask size.

## 5. The kernel works at the pre-power scale q^3

Here the scale need not be a square at the start. The actual inequalities
needed in the first-index and ratio proof follow directly from (11):

    X,Yp>=q^3>=4096,
    E=XYp>=q^6>r+1,
    a=Yp(X+1)>q^6>2r+1,
    4r/a<4/q^2<=1/64<1/2.                              (12)

These are the scale and index estimates used in the retained
[first base-two Pell argument](BASE_TWO_PELL_89_PROOF.md), Sections 2--5,
with the [fixed-minus signs](EXPLORATION_ODD_INDEX_PELL_SIGNS.md).
They replace the proof notation `n^2` by the actual common divisor `D0`.
No construction of a square root of `D0` is used.

More explicitly, the first norm has parameter `P0=2XYp^2+1`. Its index
congruence and `E>r+1` initially give an index at least `r+1`. The main
norm and the strict interval give a main Pell index at least `r+2`; this
supplies the size hypotheses of the relaxed auxiliary rank and signed
half-parameter arguments. They recover the main index `j0=2r+1`.
The same growth comparison then eliminates a positive multiple of `E`
from the first index and gives `k=psi_P0(r+1)`.

Put `xi=(X+1)^(2r)/X^r`. The ratio proof, using (12), gives

    xi<c/k<xi(1+8r/a),
    Yp>=X^r, a>X^(r+1),
    0<c/k-xi<16r/(X+1).

The exponent equation is therefore justified before exponent decoding:

    2^(3j0)=8*64^r<X^(r+1)<a, X^3<=X^r<a.

It recovers `X=2^(2r+1)`. After this, the binomial fractional tail is
strictly below `1/4` and the ratio error is below `1/2`. The strict
interval forces

    Yp=floor((X+1)^(2r)/X^r),
    D0 divides binom(2r,r).                              (13)

The last assertion uses only `D0 | X,Yp`, via the exact binomial expansion
modulo `X`. Thus a pre-power square scale was never needed.

Since `q^3 | X` and `X` is a power of two, so is `q`. The repunit equation
forces its binary exponent to be divisible by four. `P | q` and its own
alignment equation do the same for `P`, giving `q=16^N`, `P=16^h` with
`1<=h<=N`. For this decoded geometry, `D0=q^3=2^(12N)` is indeed a square,
but that conclusion was not a premise of the preceding argument.

## 6. Inverse packing types both fields without a carry gap

For `Lambda=2^e`, `0<S<Lambda`, `0<=M<Lambda`, write

    r=(Lambda-S-1)Lambda+(S+M).

If `S+M<Lambda`, then

    popcount(r)=e-popcount(S)+popcount(S+M)
               <=e+popcount(M),

with equality exactly when `S AND M=0`. If `S+M>=Lambda`, the carry into
the upper field gives the exact expression

    popcount(r)=e+popcount(M)
                 -[popcount(S)+popcount(M)-popcount(S+M)]-v2(S).

The bracket is at least one in this overflow case: disjoint supports
below `Lambda` cannot sum to `Lambda` or more. The inequality is therefore
strict. This proves the inverse-packing criterion including overflow.

At the recovered geometry, `M` has two `q`-sized blocks. Its low radix-16
digits are 13, with three set bits, and its high digits are 4, with one.
Therefore

    popcount(M)=4N, log2(Lambda)=8N,
    log2(Lambda)+popcount(M)=12N=log2(D0).                (14)

By (13), the valuation identity
`v2(binom(2r,r))=popcount(r)` reaches this upper bound. Thus `S AND M=0`.
The strict field bounds proved in Section 4 now give:

* each radix-16 digit of `C2` is zero or two, since `13=1101` forbids the
  other three bit positions;
* every radix-16 digit of `F` has bit two absent.

Dividing the first word by two proves that `C` is Boolean, with no digit
spill. Construct its actual cyclic neighbors. The local equation gives
the congruence (1). Since `0<F<q` and (2) places `Factual` strictly inside
`(0,q-1)`, invertibility of `P` modulo `q-1` gives `F=Factual`. The scalar
truth table proves Rule 110 at every cyclic cell. This completes the
soundness direction without using local truth to derive typing or bounds.

## 7. Positive completeness and fresh Pell witnesses

Suppose the supplied parameters satisfy the stated cyclic predicate.
Choose

    v=q/P, J=(q-1)/15, align=(P-1)/15,
    F=Factual, alpha=q-2C,
    z=[K(P)C+J-PF]/(q-1).

All six quantities are positive integers: `C<=J`, (2) bounds the field,
and (4) proves the quotient's strict positivity. Form `C2,Lambda,D0,S,M,r`
using the actual new source. Booleanity and the scalar truth imply
`S AND M=0`; the inverse-packing equality and (14) give
`D0 | binom(2r,r)`.

The new `r` is odd. Both `Lambda` and `S=2C+qF` are even, whereas
`M=(13+4q)J` is odd because `J` is odd. This supplies precisely the parity
needed for the fixed-minus positive auxiliary witnesses.

For completeness, the full kernel extension is obtained afresh as follows:

    j0=2r+1, X=2^j0, w=X/D0,
    Yp=floor((X+1)^(2r)/X^r), s=Yp/D0,
    a=Yp(X+1), A=a+2, Delta=A^2-1,
    E=XYp, P0=2XYp^2+1,
    c=psi_A(j0), d=chi_A(j0), k=psi_P0(r+1),
    eta=c-Yp k, zeta=k-eta,
    tau=(chi_P0(r+1)-1)/2,
    h0=(k-r-1)/E,
    gamma=(d-X-ac)/(4a+3),
    m=2c j0, f=chi_A(m), R0=Delta psi_A(m), i=R0/c^2,
    yaux=psi_R0(j0), u=chi_R0(j0)/R0,
    j=(u+j0)/c, o=(u+c)/f.                               (15)

The decoded scale and `D0<r^2<2^(2r+1)` make `w` positive integral.
Central-binomial divisibility and the binomial expansion modulo `X`
make `s` positive integral. The same exact ratio inequalities give
`0<eta<k`, and hence `eta,zeta>0`. Pell parity, index congruences, and
strict growth give positive integral `tau,h0`. The exponent congruence
gives integral `gamma`, whose numerator is positive because
`d-ac=2c-psi_A(j0-1)>c>X`.

The retained auxiliary addition identities give positive integral `i,u`
and both auxiliary norms. As `r` is odd, `j0=3 mod 4`; the fixed-minus
congruences are `u=-j0 mod c` and `u=-c mod f`. Hence `j,o` are positive
integers with `u=jc-j0=of-c`. These are all seventeen kernel coordinates,
at the actual new scale and index. This proves the complete positive
converse without importing the witness tuple of the radix-128 system.

## 8. Evidence and unresolved universal interface

The checker compares every source residual with the complete
69-instruction schedule, exhausts all sixteen scalar cases, and checks
90,036 nonzero cyclic word/stride cases at lengths one through twelve.
Exactly 33 are valid; each supplies strictly positive outer coordinates
and satisfies all six outer equations. The truth values agree with the
packed binomial valuation threshold in all 90,036 cases.

It also checks pre-power bounds at non-power values of `q`, exhausts
small inverse-packing pairs including overflow, and checks one-cell field
mask decoding. Separate exact regressions cover the main Pell equations
and positive quotients at odd `r=3,7,15,31,65`, and five small fixed-minus
auxiliary examples. These are component checks, not numerical
materializations of the enormous complete Pell witnesses in (15).
Running without `--write` recomputes the saved JSON receipt exactly.

Every valid cyclic word pulls back to a totally periodic Rule 110
space-time configuration by `c(x,t)=c_{-hx-(h+1)t mod N}`. This proves
the geometric interpretation of the relation. It does not prove that
arbitrary accepting computations have such cyclic realizations, nor does
it provide the raw-input or marker interface needed for a smaller
universal Diophantine certificate.

Independent complete scoped mathematical/source review passes, including
the strict pre-power fields, nonsquare-scale kernel argument, overflow
formula, local quotient and fresh positive converse. A fresh default
checker run reproduces the saved JSON exactly. A separately implemented
outer audit verifies all90,036 cyclic cases, the33 accepted cases and784
additional pre-power cases, including the factored equality, strict
quotient signs, actual parity and scale bounds. The independent canonical
and odd-sign Pell component checks recorded for the71 system apply to
the retained kernel; no full packed tuple is numerically materialized.
