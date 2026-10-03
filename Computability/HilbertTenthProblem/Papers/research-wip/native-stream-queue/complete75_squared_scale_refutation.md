# Deleting the cubed scale from the current complete76 admits every input

Consider the literal change to the [complete76 source](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md)
that deletes `n2=q^2*q` and uses the already computed `q^2` as the common
scale of X and Y. Keep all nineteen equalities, the strong auxiliary norm,
the main-power temporal multiplier, and the ordinary-input bridge.
The resulting source costs **75=40M+35A**, with thirty positive witnesses.

This particular75 source is false. For **every fixed compiler produced by
the complete76 construction, every positive ordinary input has strictly
positive witnesses**. In particular, a compiler for the empty set has
false positives. This extends the [older scale-deletion counterexample](../../1980/EXPLORATION_FIXED_RAW_SCALE_Q2.md)
to the current source, whose temporal multiplier is the actual main Pell
power rather than a freely chosen coordinate. The dummy-bit construction
below controls that power at the final packed index.

This is a third, distinct75 proposal. The older auxiliary-scale and
input-gap75 candidates remain open. The complete universal bound remains76.

## 1. The exact source change

Let `Lambda=q^2`, `S=Z+qF`, and `M=(MC+q*MF)J`. The outer equations remain

    (B-1)J=q-1,
    C+alpha+2d*x=q,
    (DC+B*DR+X)C=F+z(q-1),
    r=(Lambda-S)(Lambda-1)+M,
    C=Z+W.

The kernel now uses `X=w*q^2` and `Y=s*q^2`; its ten equations and four
input equations are otherwise unchanged. The [checker](complete75_squared_scale_refutation.py)
expands all nineteen residuals, including the auxiliary-norm correction,
and verifies the acyclic75-operation schedule. This is a deletion of the
scale multiplication, not a weakening of the strong auxiliary norm.

## 2. A sparse word leaves enough population for the weaker scale

Use exactly the fixed compiler of complete76. Write

    R=2^b, B=R^L=2^d, K=m+1, E=max(native positions),
    T=popcount(DC).

The fixed integers b,L,d are powers of5. There are K distinct native
positions, including Start at0, End at1, and an ignored dummy position e.
The actual masks satisfy

    popcount(MC)=d-m, popcount(MF)=m,
    MC and MF even, DR=R^H.

Here is a useful bound on the actual compiler, not on an abstract mask:

    d-m > 2(T+2).                                      (1)

Indeed, DC has two copies of at most K clause coefficients, four unit
monomials, and at most one correction monomial. Every clause coefficient
is below R, so addition cannot increase its binary population and
`T<=2Kb+5`. The compiler's separation has `L>7E`. Distinct nonnegative
positions give `E>=K-1`, hence `L>=7K-6`. Also `m=K-1` and `K>=16`.
Consequently

    d-m-2(T+2)
      >= (3K-6)b-K-13
      >= 2K-19 > 0.

Fix x>0, take h=1, and choose a power of5 N with

    N>max(25d,2x+1).

Put `q=B^N`, `J=(q-1)/(B-1)`, `W=R*B^(2x)`, and initially `C0=1+W`.
We will add a Boolean subset of the ignored dummy bit at cells0 through
N-1. Thus the final C has at most N+2 set bits, uses only native positions,
and contains End only at its intended cell. Put `Z=C-W` and define

    Cright = B*C modulo(q-1),
    F = DC*C + DR*Cright + Cright.                      (2)

The two occurrences of Cright correspond to the intended temporal shift
h=1 and the horizontal shift; they are not supplied independent fields.
Each has the same binary population as C. Therefore

    popcount(F) <= (T+2)*popcount(C)
                <= (T+2)(N+2)
                <= 2(T+2)N < (d-m)N.                  (3)

All the words used here satisfy the compiler's coefficient bounds even
though no local computation is imposed. At the aligned shift, the
unshifted R-digit contribution is at most R/2-2, and the shifted native
word contributes at most1. Each MF digit is at most R/2-2. Thus every
digit of `F+MF*J` is at most R-3; in particular it is below q. The data
mask is genuinely satisfied: `Z AND(MC*J)=0`, and `Z+MC*J<q`. We obtain

    0<S<S+M<Lambda.

For these bounds the exact packing identity is

    r=(Lambda-S-1)*Lambda+(S+M),
    popcount(r)=2dN-popcount(S)+popcount(S+M).

The two radix-q fields do not carry. The lower field also has no binary
mask carry, giving

    popcount(r)
      =2dN+(d-m)N+popcount(F+MF*J)-popcount(F)
      >=2dN.                                         (4)

No claim that the F mask vanishes has been used. This is the lost test:
the dense data mask alone provides enough population to pass the weaker
scale when F is sparse. The usual positive packing bounds also give
`q^2<=r<q^4`. Since Z is odd and MC is even, r is odd.

## 3. Control the actual main-power shift by ignored dummy bits

Let F0 and r0 come from C0 and (2). For a dummy added at a cell i with
`i+1<N`, the changes in both C and Z are `R^e*B^i`, and the change in F is

    (DC+B*DR+B)*R^e*B^i.

There is no cyclic wrap on this individual contribution. No arithmetic
carry is needed to justify these equalities: all selected native bits
obey the fixed coefficient bound. The resulting exact change in r is

    delta r = -Gamma*B^i,
    Gamma = R^e*(q^2-1)*[1+q*(DC+B*DR+B)].              (5)

The fixed compiler correction gives `2DC-DR != 0 modulo5`. Since d and N
are powers of5, the same unit calculation as complete76 gives
`Gamma != 0 modulo5`. Thus 2Gamma is invertible modulo dN.

Use the proved [five-adic subset lemma](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md)
to choose distinct cells from `i=4j`, `0<=j<N/5`, and optionally i=1,
whose weights sum to

    (2r0+1-d)*(2Gamma)^(-1) modulo dN.

Every selected cell satisfies `i+1<N`. Let C,F,Z,r now be the final words.
Equation (5) gives

    2r+1 = d modulo dN.                                (6)

All population and size bounds in Section2 hold for every Boolean subset,
so in particular they hold for this one. This is alignment at the actual
final packed r, not at an unrelated main-kernel tuple.

## 4. Complete strictly positive extension

Let `p=2r+1` and use the standard strong-kernel converse at this r:

    X=2^p,
    Y=floor((X+1)^(2r)/X^r),
    a=Y*(X+1), A=a+2, Delta=A^2-1,
    c=psi_A(p), dmain=chi_A(p).

The full converse is proved in Section5 of the older squared-scale note
linked above. Its hypotheses are odd `r>=64`, a power-of-two scale
`D0<=r^2`, and `D0 | binom(2r,r)`. Here `D0=q^2`, the packing bounds give
the first two conditions, and (4) gives the third by the exact central
binomial valuation. Since `q^2<X`, both `w=X/q^2` and `s=Y/q^2` are
positive integers. All other fifteen strong-kernel coordinates have the
unchanged positive converse. Neither the weak auxiliary candidate nor
a claim about the soundness of the q^2 kernel is needed.

Congruence (6) implies `X=B modulo(q-1)` and X>B. Let

    kR=(B*C-Cright)/(q-1) >= 0,
    z0=(DR+1)*kR >= 0,
    z=z0+[(X-B)/(q-1)]*C > 0.

Then the actual transport equation with X holds exactly. The bracket is
a positive integer. In particular z remains positive even if the sparse
word has zero ordinary wrap quotient.

The native digit bound gives `C<=(B-2)J`, hence
`q-C>=J+1>2d*x`; set `alpha=q-C-2d*x>0`. The ordinary-input bridge is
unchanged, with odd `u=2d*x+b>=3`, W=2^u and u<p. Its usual formulas are

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta,
    phi=c-kappa,
    rho=(mu-a*kappa-W)/(4a+3).

They are all positive integers by the same congruence and growth proof
as complete76. The supplied outer coordinates are also positive: Z
contains its origin bit, F is positive by (2), and the remaining bounds
were proved above. This extends the constructed outer tuple to **all
thirty strictly positive witnesses and all nineteen equations** for the
arbitrary fixed compiler and arbitrary x>0.

## 5. Evidence boundaries

The checker audits the complete modified source, proves the population
identity symbolically, and checks (1) on several actual complete76
compiler layouts, including both correction branches. It materializes
illustrative sparse outer tuples with `B=32`, `N=625`, actual packed-index
alignment and nonzero forbidden F bits. These modest fixed masks are
explicitly not the full universal compiler. Their huge main and auxiliary
Pell values are given by the positive formulas, not materialized.

The all-compiler and all-input assertions are the mathematical proof
above. Neither finite layouts nor illustrative tuples substitute for it.
The [receipt](complete75_squared_scale_refutation.json) is checked by
default. Two independent full proof/source/default reviews passed, including
the actual compiler bounds, final-index alignment, and every strictly
positive extension coordinate.
