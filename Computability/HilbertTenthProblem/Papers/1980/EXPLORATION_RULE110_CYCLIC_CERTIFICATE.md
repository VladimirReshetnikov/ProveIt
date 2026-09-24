# A 71-operation certificate for a parametrized cyclic Rule 110 relation

For three supplied positive parameters `q,P,C`, this note gives a complete
positive Diophantine certificate with **71=40M+31A**, 23 positive
existential unknowns, and 16 equations, for the following exact predicate:

* `q=128^N` and `P=128^h` for integers `1<=h<=N`;
* `C=sum_{i=0}^{N-1} c_i 128^i` is a nonzero Boolean word;
* with all indices modulo `N`,

      c_{i-h-1}=Rule110(c_{i+h},c_i,c_{i-h}) for every i.

The parameters together with the existential unknowns give 26 positive
supplied coordinates. Numerals and equality comparisons are free, and
every multiplication or addition/subtraction is charged. Powers shown
in the mathematical definitions are constructed by the source schedule.

This is a different relation from the numerical endpoint relation of the
[75-operation finite-history system](EXPLORATION_ZERO_OFFSET_RULE110_HISTORY.md).
It has no prescribed input, output, marker, halting, or acceptance
interface. In particular, this is not a 71-operation universal certificate
and does not improve the established universal bound by itself.

The [checker](../verification/explore_rule110_cyclic_certificate.py) and
[receipt](../verification/explore_rule110_cyclic_certificate.json) include
the complete source, exact polynomial comparisons, and finite regressions.
They do not attempt to materialize an enormous complete packed Pell
witness; its existence follows from the constructive converse below.

## 1. The zero-offset local field and cyclic convention

For Boolean `l,c,r,y`, put

    phi(l,c,r,y)=18l+23c+23r+42y.

The exact scalar table is

| l c r | Rule 110 output | phi at y=0 | phi at y=1 |
|---|---:|---:|---:|
| 000 | 0 | 0 | 42 |
| 001 | 1 | 23 | 65 |
| 010 | 1 | 23 | 65 |
| 011 | 1 | 46 | 88 |
| 100 | 0 | 18 | 60 |
| 101 | 1 | 41 | 83 |
| 110 | 1 | 41 | 83 |
| 111 | 0 | 64 | 106 |

Thus `phi AND 36=0` exactly for the correct output, and every raw value
lies in `[0,106]`. Rule 110 also satisfies the pointwise implication

    y=Rule110(l,c,r)  =>  y<=c+r.                         (1)

Write `B=128`, `D=q-1`, and `J=(q-1)/127` once the geometry is established.
For a Boolean word `C`, define the actual left, right, and next words by

    L_i=c_{i+h}, R_i=c_{i-h}, Y_i=c_{i-h-1}.

Modulo `D`, their word values are `P^(-1)C,PC,BPC`, respectively. Define

    Factual=18L+23C+23R+42Y,
    K(P)=18+P[23+(23+42B)P].                             (2)

Multiplying the first formula by `P` gives the exact congruence

    P Factual == K(P) C  (mod D).                       (3)

There is no cell carry: each raw digit of `Factual` is at most 106.
Moreover, if `C>0`, then

    0<23C<=Factual<=106J<D,  C+Factual<=107J<q.           (4)

This proves the strict size bounds needed in the converse. It also means
that a supplied `0<F<q` satisfying (3) must equal `Factual`: multiplication
by `P` is invertible modulo `D`, and the nonzero residue `Factual` lies
strictly between zero and `D`.

## 2. The local quotient is strictly positive on every valid word

For any Boolean nonzero word, define nonnegative integer wrap quotients

    P L=C+kL D,  R=PC-kR D,  Y=BPC-kY D.

Here `0<=kL<P`, because both `C` and `L` are strictly between zero and
`D`; also `kR,kY>=0`. The exact difference in (3) is

    K(P)C-P Factual
       =[P(23kR+42kY)-18kL]D.                           (5)

For a valid Rule 110 word, (1) gives `Y<=C+R<=C+PC`. If `kY=0`, then
`Y=BPC`, contradicting `BP>1+P`, since `C>0` and `P>=B`. Hence `kY>=1`,
and the quotient `z` in (5) satisfies

    z>=42P-18(P-1)=24P+18>0.                            (6)

Consequently the local equality can use one positive unknown `z`, without
expressing a signed integer as a difference of two positive unknowns.
The quotient need not be positive for invalid Boolean words. Positivity
is used for completeness only after the actual local truth is known.

## 3. Complete equations and operation ledger

In addition to the parameters `q,P,C`, supply six positive outer unknowns

    v,J,align,F,alpha,z

and seventeen positive kernel unknowns

    a,c,d,f,h0,i,j,k,o,r,s,w,tau,eta,zeta,gamma,yaux.

The source uses the names `Jrep,zquot,h,ga,y_aux` for `J,z,h0,gamma,yaux`.
The kernel coordinates `c,r` are distinct from the Boolean cell symbols.
Construct

    n=q^2, n2=n^2,
    S=C+qF,
    T=(36q+126)J, Tplus=T+1.                             (7)

The six outer equations are

    127J=q-1,
    Pv=q,
    127align=P-1,
    C+F+alpha=q,
    K(P)C=PF+z(q-1),
    r=S(n2-n)+Tplus(n2-1).                              (8)

For `X=wn2`, `Yp=sn2`, `Delta=a^2+4a+3`, and `u=jc-(2r+1)`, the ten
retained fixed-minus kernel equations are

    XYp^2(XYp^2+1)k^2=tau(tau+1),
    c=Yp k+eta,  k=eta+zeta,  k=r+1+h0 X Yp,
    a=Yp(X+1),  d=X+ac+gamma(4a+3),
    d^2=Delta c^2+1,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-yaux^2)=1-yaux^2,
    u=of-c.                                             (9)

The computed register `u` may have either sign in a putative solution;
it is not an additional supplied positive unknown.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry: `q-1,127J,Pv,P-1,127align` | 3 | 2 | 5 |
| Bound: `C+F+alpha` | 0 | 2 | 2 |
| Local coefficient `K(P)` | 2 | 2 | 4 |
| Local equality: `KC,PF,z(q-1),PF+z(q-1)` | 3 | 1 | 4 |
| Powers `n=q*q,n2=n*n` | 2 | 0 | 2 |
| `S=C+qF` | 1 | 1 | 2 |
| `Tplus=(36q+126)J+1` | 2 | 2 | 4 |
| Packed index equation | 2 | 3 | 5 |
| Outer subtotal | 15 | 13 | 28 |
| Retained fixed-minus kernel | 25 | 18 | 43 |
| **Complete source** | **40** | **31** | **71** |

In particular, packing including its two powers costs **13** operations.
The retained 43-operation kernel assumes `n2` has already been computed;
the multiplication `n2=n*n` is paid in the outer subtotal. The reduction
uses the proved positive quotient, rather than an omitted signed adapter
or an uncharged power.

The checker expands all 71 primitive instructions and compares the 16
source residuals. The only triangular correction is in the auxiliary
norm: the preceding residual `[(ic^2)^2-Delta(f^2-1)]` multiplied by
`(u^2-yaux^2)`. Its preceding equation is compared exactly, so the source
equalities and certificate equalities are equivalent in both directions.

## 4. Bounds before any power, mask, or local-rule decoding

Take an arbitrary positive solution of (8)--(9). The repunit and
alignment equations imply `q>=128` and `P>=128`; divisibility gives
`P<=q`. The positive bound gives `C,F<q`. Without assuming that `q` is a
power, two exact identities give the required packed-field bounds:

    n-S=(q-1)C+q alpha>0,
    n-Tplus=J[(B-37)q+1]>0.                              (10)

The second uses `q-1=(B-1)J` and `B=128`. Thus `0<S,Tplus<n`, and

    n>=64,  n<=r<2n^3.                                  (11)

For the lower bound it suffices that `Tplus>=1`, `S>0`, and
`r>=n^2-1>=n`. The upper bound follows directly from (8).
No typing, radix alignment, local truth, or parity assumption entered
these estimates.

The first-index, exponent, and rounding part of the
[base-two Pell proof](BASE_TWO_PELL_89_PROOF.md), Sections 2--5, uses only
`n>=64`, `n<=r<3n^3`, and the displayed first kernel equations. Its second
exponent block and its compiler-specific conditions are unnecessary here.
The [fixed-minus signs proof](EXPLORATION_ODD_INDEX_PELL_SIGNS.md) applies
to the changed two expressions for `u` and permits an arbitrary signed
`u` during soundness. For clarity, the actual scale inequalities here are

    X,Yp>=n^2, E=XYp>=n^4>r+1,
    a=Yp(X+1)>n^4>2r+1,
    4r/a<8/n<=1/8<1/2.                                  (12)

They justify the first Pell index and ratio arguments before any exponent
decoding. Those arguments recover the main index `j0=2r+1` and
`k=psi_(2XYp^2+1)(r+1)`. Writing

    xi=(X+1)^(2r)/X^r,

the ratio argument gives `Yp>=X^r`, `a>X^(r+1)` and
`0<c/k-xi<16r/(X+1)`. Thus the exponent equation in (9) satisfies its
growth hypotheses already:

    2^(3j0)=8*64^r<X^(r+1)<a,  X^3<=X^r<a.

It proves `X=2^(2r+1)`. Exact binomial rounding then proves

    Yp=floor((X+1)^(2r)/X^r),
    n^2 divides binom(2r,r).                             (13)

Here the fractional binomial tail is less than `1/4`, and the ratio error
is less than `1/2` after `X=2^(2r+1)`; the two strict interval inequalities
force the exact floor. This is the same retained kernel conclusion at
the actual new `n,r`, without a second-exponent interface.

Since `X=wn^2` is a power of two and `n=q^2`, the integer `q` is a power
of two. The congruence `127 | q-1` forces its binary exponent to be a
multiple of seven. Similarly, `P | q` and `127 | P-1` prove

    q=128^N, P=128^h, 1<=h<=N.                           (14)

For example the elementary divisibility assertion follows by writing
the binary exponent as `7t+s`, `0<=s<7`, and reducing modulo 127:
`2^s-1` lies in `[0,126)` and hence must be zero.

## 5. The packed mask recovers Booleanity and the exact local field

Let `n=2^e`. For arbitrary integers `0<S<n` and `0<=T<n-1`, direct
base-`n` expansion gives

    r=(S+T)n^2+(n-1-S)n+(n-1-T).

The two lower digits belong to `[0,n)`, while the higher value `S+T`
is allowed to exceed `n`. Therefore

    popcount(r)=2e-[popcount(S)+popcount(T)-popcount(S+T)]
               <=2e,                                   (15)

with equality exactly when `S AND T=0`. This includes the case
`S+T>=n`; there is no hidden disjointness or no-overflow assumption.
The valuation identity `v2(binom(2r,r))=popcount(r)` and (13) force
equality, since `n^2=2^(2e)`.

At the recovered radix, the two `q`-sized fields of `T` are `126J` and
`36J`; those of `S` are `C,F`, already known to be below `q`. Each digit
of `126J` is `126=1111110` in binary, so the first mask types every
radix-128 digit of `C` as zero or one. The second mask forbids bits two
and five in every digit of `F`.

Now construct the actual rotated Boolean words from `C`. By (3) the
source equality gives `F==Factual (mod q-1)`. By (4) and `0<F<q`, it gives
the integer equality `F=Factual`. The scalar truth table then proves the
Rule 110 relation at every cyclic cell. This proves soundness in exactly
the three supplied parameters, without assuming local truth during the
power, range, or Booleanity steps.

## 6. Complete positive converse at the actual new index

Suppose `q,P,C` satisfy the predicate at the beginning of the note.
Choose

    v=q/P, J=(q-1)/127, align=(P-1)/127,
    F=Factual, alpha=q-C-F,
    z=[K(P)C-PF]/(q-1).

All six are positive integers by (4), (6), and the geometry. Form the
actual `n,S,Tplus,r` in (7)--(8). Mask disjointness and (15) give
`popcount(r)=2 log2(n)`, hence `n^2 | binom(2r,r)`. Also `r` is odd:
`n` is even, `S(n^2-n)` is even, `T` is even, and `Tplus(n^2-1)` is odd.
These parity statements use the actual mask and index, not a previous
history construction.

Here is the full fresh kernel extension. Put

    j0=2r+1, X=2^j0, w=X/n^2,
    Yp=floor((X+1)^(2r)/X^r), s=Yp/n^2,
    a=Yp(X+1), A=a+2, Delta=A^2-1,
    E=XYp, Q=XYp^2, P0=2Q+1,
    c=psi_A(j0), d=chi_A(j0), k=psi_P0(r+1),
    eta=c-Yp k, zeta=k-eta,
    tau=(chi_P0(r+1)-1)/2,
    h0=(k-r-1)/E,
    gamma=(d-X-ac)/(4a+3).                              (16)

The powers of two and `n^2<=r^2<2^(2r+1)` make `w` positive integral.
The exact binomial expansion modulo `X` and central divisibility make
`s` positive integral. The strict ratio bounds used above give
`0<eta<k`, so `eta,zeta>0`. The odd base `P0` makes `tau` integral;
the index congruence gives integral `h0`, which is positive by strict
Pell growth. The base-two exponent congruence makes `gamma` integral;
its numerator is positive because

    d-ac=2c-psi_A(j0-1)>c>X.

To supply the remaining auxiliary coordinates, set

    m=2c j0, f=chi_A(m), R0=Delta psi_A(m), i=R0/c^2,
    yaux=psi_R0(j0), u=chi_R0(j0)/R0,
    j=(u+j0)/c, o=(u+c)/f.                              (17)

The retained Pell addition identities give positive integral `i,u` and
the two norm identities in (9). Since `r` is odd, `j0=3 mod 4`; the
fixed-minus polynomial congruences give `u=-j0 mod c` and `u=-c mod f`.
Thus `j,o` are positive integers and satisfy `u=jc-j0=of-c`. In particular,
all seventeen kernel unknowns are freshly supplied and positive. These
formulas, together with the six outer choices, prove necessity for the
actual new `n,r`; no old Pell tuple is reused.

## 7. Scope and finite evidence

The word pulls back to a valid totally periodic Rule 110 space-time
configuration by

    c(x,t)=c_{-hx-(h+1)t mod N}.

This is the same surjective cyclic pullback as in the
[consecutive-convolution note](EXPLORATION_BOOLEAN_CONSECUTIVE_CONVOLUTION.md).
It is an exact geometric interpretation, not a universal acceptance
interface. In particular, arbitrary accepting Rule 110 computations are
not shown to possess consecutive-period torus realizations.

The receipt checks all sixteen scalar cases; all 90,036 nonzero Boolean
cyclic words of lengths `1,...,12` at strides `1,...,N`; and every one of
their exact affine fields, signed quotients, packed valuations, mask
results, and truth values. Exactly 33 of these word/stride cases are
valid, and all 33 have strictly positive quotients and satisfy all six
outer source equations with positive supplied coordinates. Invalid words
include quotients of every sign, confirming that the positivity argument
must use actual local truth.

Separate regressions test the pre-power identities at non-power values,
the carry formula at arbitrary small packed pairs including `S+T>=n`,
and exact main Pell choices at odd `r=3,7,15,31,65`. Five independent small
auxiliary choices test the fixed-minus quotient signs. These are exact
component regressions, with no claim that they numerically instantiate
the enormous full kernel extension of a packed accepted word. The
constructive proof of that extension is Section 6. Running the checker
without `--write` recomputes and compares the saved JSON receipt exactly.

Independent full scoped mathematical/source review passes. In addition to
the fresh default receipt comparison, a separate implementation verifies
all90,036 outer cyclic cases and the33 valid cases, including the two
pre-power identities, local truth, packed valuation and actual odd parity.
Fresh independent checks also preserve the sources and receipts of the
eight-case canonical Pell regression and five-case odd auxiliary
regression. A further exact odd main-index check at r=65 passes with
million-bit coordinates. These remain component checks; the full positive
extension for arbitrary accepted parameters is the argument in Section6.
