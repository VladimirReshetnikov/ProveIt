# Refuted candidate: 89 arithmetic operations with n=q^5 and a bound on S

**Status: arithmetic PASS, intended representation REFUTED.** The exact
arithmetic certificate below has 89 operations, and the preliminary Pell
recovery and canonical necessity arguments hold. Sufficiency is false for
this compiler: `EXPLORATION_PACKED_BOUND_Q5_COUNTEREXAMPLE.md` constructs
an admissible index of an inconsistent circuit for which all 22 equations
have positive witnesses at x=1. An overflowing Tplus preserves the central
binomial condition while admitting false codes. This does not replace
the published 90-operation construction or rule out other encodings.

## 1. Source changes and exact arithmetic count

Start with the binary product system of `BINARY_PRODUCT_90_PROOF.md`,
including its fixed coefficient compiler and complete base-two Pell
block. Write

    C=x+g, Omega=e-ell, sigma=Omega*C^2,
    S2=ell+e*q,
    S=g+q^2*(S2+q^2*sigma),
    Tcoef=1+theta*lambda,
    Tplus=q^2*Tcoef+ell*(theta*q^4-b),
    r=S*(n^2-n)+Tplus*(n^2-1).

The source uses the product polynomial (e-ell)C^2 in the displayed S
and T-independent packed-r expression. The separate product equality
identifies it with the supplied positive sigma. Replace exactly

    n=q^8, ell+sigma+alpha=q

by

    n=q^5, S+alpha=n.                            (1)

All supplied unknowns remain positive. There are still 34 unknowns,
22 equations, and the fixed inputs (V,H,Tindex) besides queried x.

In the exact round37 instruction list, replace q8=q4*q4 by q5=q4*q,
delete bound_sum=ell+sigma, and move the retained bound addition to
immediately after S, where it now reads L1=S+alpha. Change the free
equalities n=q8 and L1=q to n=q5 and L1=n. There is no new operation
in either the powers or the retained Pell block. The total becomes

    89 = 48 multiplications + 41 additions/subtractions.

`../verification/round38_1980_packed_bound_candidate.py` states all
22 source residuals afresh and verifies every primitive instruction
and equality, including the three inherited acyclic corrections.
Its JSON status separates arithmetic_status PASS from
universality_status REFUTED_FOR_CURRENT_COMPILER. Literal numerals
remain {1,3,4}, all free.

Relative to round37, the only changed source residuals, in zero-based
order, differ by

    0: S-ell-sigma+q-n,
    5: q^8-q^5.

The shared-register value L1 is the only changed common register;
q8 and bound_sum disappear and q5 is added. The retained source
corrections are exactly

    correction2=-lambda*F3,
    correction16=F15*(u_aux^2-y_aux^2),
    correction17=F3*(kappa+rho*(F3-2*(A-B))),

where u_aux=2r+1+jc. Residuals F3,F15 are independently exact.

## 2. Bounds before any Pell or coefficient decoding

All fixed-index conditions from the binary compiler are retained:

    H=H0-1, theta=H+b=B-2,
    B=H0+1+b, b=x+beta,
    lambda*(B-1)=q^2-1.

Here H0 is the same fixed power of two, larger than 1024 and 3L.
Since lambda>=1, geometry gives B<=q^2, and B>H0>1024 gives
q>32. Also 3L<B<=q^2<n=q^5.

Positive sigma and C imply Omega=e-ell>=1. The new bound gives
0<S<n. Each summand of

    S=g+q^2 ell+q^3 e+q^4 sigma

is positive. Therefore, without using any decoded digits,

    0<sigma<q, C^2<=sigma<q, 0<g<C<sqrt(q),
    0<ell<e<q^2, S2<q^3.                       (2)

Since theta=B-2=H0+b-1>b, the coefficient theta*q^4-b is positive,
and consequently Tplus>0. Geometry gives Tcoef=q^2-lambda<q^2,
so

    Tplus<q^4*(1+theta*ell)<q^4*S<q^4*n.       (3)

For the second inequality, theta<q^2 and the positive summands of S
give S>1+theta*ell. Hence the packed-r equation yields

    n^2-1<=r<2*q^4*n^3=(2/q)*n^4<n^4/16.      (4)

The last inequality uses q>32. In particular r>=n, since n is huge.
These bounds do not assert Tplus<n.

## 3. Exact Pell recovery remains valid

Use the retained definitions

    U=w*n^2, Y=sP*n^2, E=UY,
    a=Y*(U+1), A=a+2, Dpell=A^2-1,
    P=2UY^2+1, J=2r+1.

Positive w,sP give U,Y>=n^2, E>=n^4, and a>n^4. Equation (4)
therefore proves

    E>r+1, a>J.

Classification of the first and main norms, together with the first
index congruence and positive interval, gives positive indices t,p,
with t>=r+1 and p>=t+1>=r+2>=66. Thus c=psi_A(p)>A*Dpell^2
and c>J. These are the independent hypotheses of the retained
relaxed-norm and half-parameter index proof. That proof now recovers
p=J before any exponential or coefficient decoding.

The first index is t=r+1. Its exclusion argument uses E>r and the
unchanged inequality

    (2P-1)-4A=4Y*(U*(Y-1)-1)-7>0,

so it does not require the older r<2n^3 bound.

The lower ratio estimate in `BASE_TWO_PELL_90_PROOF.md` is unchanged.
The upper estimate needs 4r/a<1/2; the new bounds give the stronger

    4r/a<8/q<1/4.

Consequently its two estimates still read, for
xi=(U+1)^(2r)/U^r,

    xi<c/k<xi*(1+8r/a),
    Y>=U^r, a>U^(r+1),
    0<c/k-xi<16r/(U+1).                       (5)

The first exponent criterion therefore gives U=2^J exactly as in
that proof. Its size conditions use U>=n^2, r>=n>=64 and (5), not
the old particular definition of n. In particular n, and hence q
from n=q^5, are powers of two.

The fixed-index congruence kappa=psi_2(L)+Delta*a and the second
Pell norm/gap identify the second index as L. Here 0<L<J follows
from 3L<B<=n<=r, and the same small psi_2 values are below a.
The second exponent criterion has the same sufficient size bounds:

    B^(3L)<=B^B<=n^n<=U^r<a<A,
    q^3<=n^n<=U^r<a<A.

It yields q=B^L, so B is a power of two. Finally the exact base-two
binomial-tail estimate and (5), after U=2^J, prove that Y is the
integer binomial polynomial value. Thus

    n^2 divides binom(2r,r).                  (6)

All conclusions through (6) precede coefficient decoding. This
establishes the modified bootstrap, not the missing mask implication.

## 4. The failed sufficiency step

The ordinary packing lemma requires both S<n and T=Tplus-1<n to
deduce S AND T=0 from (6). Equation (1) gives the first range but
(3) gives only Tplus<q^4 n. The second range has not been proved.

Moreover (2) bounds ell,e only by q^2, so the old canonical-code
decoding cannot be invoked to prove that range before extracting
the masks. The fact that canonical ell,e have short support is a
necessity statement and is not an available sufficiency hypothesis.
The companion counterexample proves that this is a real failure, rather
than only a missing bound. It takes noncanonical codes

    ell=ell_c+v*q, e=e_c+v*(q-1),

and chooses v to preserve the fixed-index congruence while repairing
both false coefficient windows. The effective third packed coordinate
becomes D*C^2-v*(C^2-1). Writing Tplus-1=a_over*n+t, the construction
gives S AND t=0 and S AND a_over=0. The exact four base-n digits then
yield popcount(r)=2*log2(n), so the retained binomial test still passes.
Every positive Pell witness extends to this new r. Thus an empty-set
index admits x=1.

The earlier common shift by m q^2 is excluded by S<n=q^5. The new
asymmetric shift demonstrates why excluding that one family did not
establish canonicality. The full proof and focused exact regression
are separate from the arithmetic and preliminary bounds recorded here.

## 5. Canonical positive necessity

Given an actual represented solution, use exactly the binary
coefficient compiler and fixed index of the 90-operation proof.
Choose its physical nonnegative witnesses and forbidden-bit splits,
set delta=1 and its helpers/copies correctly, and choose B an
arbitrarily large power of two after these finite values. The same
support and small-coefficient conditions give

    ell=ell0(B), e=e0(B), sigma=D(B)C(B)^2,
    0<sigma<q=B^L, S2<q^2, 0<g<q,
    theta*ell<q,

and all three binary masks pass. These statements are now legitimate
because the witnesses are the constructed canonical ones.

Set n=q^5. Since sigma<=q-1 and q^2*S2+g<q^4,

    S=q^4*sigma+q^2*S2+g<q^5=n.

Thus alpha=n-S is a positive integer satisfying the new bound.
Also the integer inequality theta*ell<q gives 1+theta*ell<=q,
and the strict estimate

    Tplus<q^4*(1+theta*ell)<=q^5=n

supplies the required canonical packing range. Both S and Tplus
are positive, so n^2-1<=r<2n^3. The established masks and this
range give (6) by the usual packing lemma.

The canonical g and ell have zero base-B unit digits. Therefore
S,Tplus,r are even, also for n=q^5. The positive necessity
construction of `BASE_TWO_PELL_90_PROOF.md` applies with these new
n,r, supplying all first/main/second and relaxed/half-parameter
witnesses, including the strict positive quotients and J=1 modulo
four condition. These witnesses are recomputed; the old n=q^8
Pell witnesses are not reused. Every one of the candidate's 34
supplied unknowns is positive.

Thus canonical necessity is proved, but complete sufficiency is false
at the mask-extraction step in Section 4.
