# A full false-code family for the q5 packed-bound candidate

This note refutes the intended representation theorem for the round38
candidate with the current compiler. Its 89-operation arithmetic certificate remains
an exact certificate for the candidate equations, but those equations
do not represent the intended sets. The 90-operation system is unchanged.

The candidate retains sigma=(e-ell)C^2 and the old packed expressions,
but replaces the bounds by n=q^5 and S+alpha=n. The alias below passes
the full system at the fixed index of an inconsistent circuit. Its
overflowing T is precisely what the bound on S alone fails to exclude.

## 1. The fixed inconsistent circuit and full physical assignment

Use the binary compiler of `BINARY_PRODUCT_90_PROOF.md`. Add the
inconsistent final zero equation

    2 delta delta_copy=0,

where delta_copy is a fresh square-difference copy of delta. In the
correct compiler delta=delta_copy=1, so this represented set is empty.
Place its negative row before its positive row. Both signs are required
but their order is a free compiler choice. Their main targets are
t_minus<t_plus. Retain the final two unit rows after this pair.

Set the queried input to x=1. Assign every helper, guard, and copy its
usual necessity value: V0=V1=X=Y=Z=1,delta=delta_copy=1,u=0. Give
all ordinary circuit coordinates their corresponding values. The only
false main rows are the designated -2 and +2. All helper and extra
negative-coefficient targets have value zero. Split the physical
values by the same forbidden-bit rule and set every dummy to zero.

Keep delta at the first non-input weight w0=8 and all other non-input
weights among 8*7^i for i>=1. Thus the FULL canonical physical
polynomial is

    C(T)=1+T^8+terms of degree at least 56,

with nonnegative coefficients, and

    C(T)^2-1=2T^8+positive terms of higher degree. (1)

It is not being replaced by the two-term polynomial 1+T^8: all
helpers and ordinary values remain present. Every exponent in (1)
is zero modulo eight and the degree is at most 2M, where M is the
largest true physical weight.

Let ell0,e0,D=e0-ell0 be the actual binary compiler polynomials.
Use its usual support constants, with K=t_last+3 and L>3K+2 a
power of two. All target windows end at K-1. The highest D term is

    T^(t_last-4)=T^(K-7), with coefficient +1. (2)

All D coefficients are in {-1,0,1}. Choose the admissible fixed
index H=H0-1,V=ell0(2)+2^L e0(2),Tindex=psi_2(L), with every
published H0 threshold. This index is fixed before choosing B.

## 2. A positive change smaller than D(B)

Choose B an arbitrarily large power of two after the physical values
are fixed. Write b=B-H0-1,theta=B-2,q=B^L. Require B>=4H0 and
the usual canonical small-coefficient bounds. Put

    v0=B^(t_plus-8)-B^(t_minus-8)>0,
    E0=K-8, R=(B-2)/2=B/2-1.

Here R is odd and coprime to B. Choose 0<=k<R so that

    v=v0+k B^E0=0 modulo R.                   (3)

The inverse of B^E0 modulo R exists. The two false targets precede
the final unit rows, so t_plus-8<E0-1 and v0<B^E0. Equation (2)
and the coefficient bound on D give

    D(B) > [(B-2)/(B-1)] B^(E0+1),
    0<v<(B/2+1)B^E0<D(B)                     (4)

for B>=8. Thus the changed product factor D(B)-v is positive.

The correction of the tested value is

    v0(C(T)^2-1).

At t_minus, its negative term has coefficient -2, so subtracting
it repairs the original -2 to zero. At t_plus, its positive term
has coefficient +2, so subtracting it repairs the original +2 to
zero. Every other term from either shift lies strictly after that
row's main target and no later than t+2M. All starts within the
same row band are at most t. The next row band's earliest reset
is beyond t+10M-4, since the target spacing is 12M+8. Hence these
other terms affect no tested start, following window digit, or reset.
They are zero modulo eight, whereas every reset has residue four.

The high adjustment kT^E0 first affects its product with C(T)^2-1
at E0+8=K. Therefore it changes no tested coefficient or incoming
carry at any position through K-1. Signed carries travel toward
higher positions only. Below K the finitely many added coefficients
are independent of B, so B can be chosen to make their absolute
values small. All unchanged positive resets clear the signed carries
exactly as in the compiler proof. Consequently every tested digit of

    D(B)C(B)^2-v(C(B)^2-1)                    (5)

is binary, with both false windows now (0,0,0).

## 3. The noncanonical positive codes and the source equations

Write ell_c=ell0(B),e_c=e0(B),C=C(B),g=C-1,D_B=D(B). Define

    ell=ell_c+vq,
    e=e_c+v(q-1),
    sigma=(D_B-v)C^2,
    sigma_eff=sigma+v=D_B C^2-v(C^2-1).       (6)

Then e-ell=D_B-v>0 and sigma>0. Since v>0 and C>1,

    0<sigma_eff<D_B C^2<q,

where the last bound follows by choosing B large with the fixed
degree bound deg(D C^2)<3K<L. The supplied codes are positive,
and their middle expression is exactly

    ell+eq=ell_c+e_c q+v q^2.                 (7)

Equation (3) and the factor two in q^2 imply theta divides vq^2.
Thus the fixed-index congruence is preserved; its quotient is the
canonical positive quotient plus the positive integer vq^2/theta.

Let S2_c=ell_c+e_c q and set n=q^5. The exact packed input becomes

    S=g+q^2 S2_c+q^4 sigma_eff.               (8)

Here g<q, S2_c<q^2, and sigma_eff<q. Integrality gives S<n,
so alpha=n-S is positive and satisfies the candidate's bound.
Supply the usual positive beta=b-1 and geometric lambda. Every
changed coding equation is now satisfied with positive unknowns.

## 4. Low masks and the extra high block

For T=Tplus-1, the exact expression is

    T=a_over*n+t,
    a_over=theta*v,
    t=(q^2-1-b ell_c-b v q)+q^2 theta lambda
                                  +q^4 theta ell_c. (9)

All terms used here are integers. The degree bounds give
b ell_c<q, bv<q/B, and theta*v<q. Thus the first parenthesis is
positive and below q^2. Also theta lambda<q^2 and theta ell_c<q.
Consequently 0<=t<n and a_over>0, so T>n.

The first low mask differs from its canonical value only by -bvq.
The least nonzero base-B position of v is t_minus-8>M+1. Its
product by b cannot lower that position, so this subtraction starts
above L and above every nonzero position of g. No borrow propagates
toward lower digits. Therefore the first low mask still passes.

The middle low mask theta lambda is unchanged, and its coordinate
is exactly S2_c, so it passes. The third low mask is theta ell_c
and its coordinate is (5), whose full indicator tests pass by
Section 2. The genuine low block decompositions of (8)--(9) therefore
give the exact binary nonintersection

    S AND t=0.                                (10)

There is a second nonintersection. Since a_over=theta*v<q and its
least nonzero position is greater than M, it has no bits in common
with g. Every other summand of S starts at position 2L or later,
whereas a_over<q ends before L. Hence

    S AND a_over=0.                           (11)

These statements concern the actual normalized integers; no raw-
coefficient support lemma is substituted for a binary mask.

## 5. Exact popcount despite overflow

Let n=2^N. For any S,t,a with 0<S<n,0<=t<n,0<a<n and
S AND t=S AND a=0, both S+t and S+a are below n. For

    r=S(n^2-n)+(an+t+1)(n^2-1),

the exact base-n digits, from highest to lowest, are

    a, S+t, n-S-a-1, n-t-1.

All four are valid digits. Using the complement identity
popcount(n-z-1)=N-popcount(z) gives

    popcount(r)=2N+popcount(a)+popcount(S+t)
                          -popcount(S+a)-popcount(t)=2N. (12)

The last equality uses the two nonintersections. Our values satisfy
all these hypotheses by (8)--(11), so the central-binomial valuation
identity proves n^2 divides binom(2r,r), even though T>n.

The generic candidate bounds also apply: S<n,Tplus<q^4S give
n^2-1<=r<2q^4n^3. Both g and ell are divisible by B, so S,Tplus
and r are even. The powers B,q,n and the fixed L are already
canonical. The false-code construction has therefore supplied the
exact powers, binomial divisibility and parity needed next.

## 6. Complete positive Pell extension without assuming T<n

Recompute every Pell witness for this new r. Set

    J=2r+1, U=2^J,
    xi=(U+1)^(2r)/U^r, Y=floor(xi),
    w=U/n^2, sP=Y/n^2,
    a=Y(U+1), A=a+2, Dpell=A^2-1, E=UY, P=2UY^2+1,
    c=psi_A(J), d=chi_A(J), kP=psi_P(r+1).

The power U is divisible by n^2, because n is a power of two and
n^2<=r+1<U. The exact base-two binomial tail is between zero and
1/4. Equation (12) consequently gives n^2 dividing Y, so w,sP
are positive integers.

For clarity, the ratio estimate is justified anew and does not use
the old r<2n^3 hypothesis. Since Y>=U^r,

    a>U^(r+1), 4r/a<4r/U^(r+1)<1/2.

The same elementary lower and upper Pell estimates therefore give

    xi<c/kP<xi+16r/(U+1)<Y+3/4.

Here U=2^(2r+1)>32r, and xi>Y. Thus eta=c-YkP and
zeta=(Y+1)kP-c are positive. The choices

    tau=(chi_P(r+1)-1)/2,
    h_index=(kP-r-1)/E

are positive integers and satisfy the first norm and index equation.
The main norm holds by construction. The first exponent quotient
gamma is integral from U=2^J and positive because
d-a c=2c-psi_A(J-1)>c>U.

For the second index use

    kappa=psi_A(L), mu=chi_A(L),
    Delta=(psi_A(L)-psi_2(L))/a, phi=c-kappa.

These are positive integers with 2<=L<J. Polynomial congruence
modulo a gives the integrality of Delta. The second exponent
congruence holds for q=B^L; its quotient rho is integral and positive
since mu-(A-B)kappa>(B-1)kappa>q. Its modulus is positive because
A is larger than B and q. The usual sufficient size bounds follow
from U>=n^2,r>=n,3L<B<=n and a>U^(r+1).

Finally apply the explicit relaxed/half-parameter positive witness
construction of `HALF_PARAMETER_PELL_92_PROOF.md` at this A and J,
as retained by `BASE_TWO_PELL_90_PROOF.md`. Even r gives J=1 modulo four. Thus
its index m=2cJ, f=chi_A(m), i=Dpell*psi_A(m)/c^2, and normalized
odd-root witnesses have the required divisibility and strictly
positive o,j,y_aux, exactly as in the published generic lemma.
That construction depends on these Pell indices and parity, not
on T<n or canonicality of the supplied coefficient codes.

All 34 supplied unknowns of the q5 candidate are now positive and
all 22 source equations hold. Its fixed index represents an empty
set, yet x=1 is admitted. This disproves that candidate's intended
universality with the current compiler.

## 7. Exact finite corroboration and evidence scope

`../verification/explore_packed_bound_q5_counterexample.py` reuses
the actual round37 sample layout and swaps the entire two false-row
bands so the negative row comes first. The unchanged symbolic
compiler checks pass on that reordered layout. It uses the full
physical assignment at x=1, including every nonzero helper and
ordinary coordinate.

Three sparse cases check both original failures, exact cancellation
of the false rows, every extra/helper target and reset, all 397
normalized binary indicator digits, and the modular CRT correction
with the actual support exponents. They also check the degree and
leading-digit inequalities needed for 0<v<D(B) and disjoint low
supports. A separate 13,230-case exact integer regression verifies
the overflow identity (12).

The sample's zero=1 assignment is a false assignment, not a proof
that its particular represented input has no other valid assignment.
The separate inconsistent delta*delta_copy row in Section 1 supplies
the actual nonmembership argument. No astronomical full Pell witness
is materialized by the finite checker; Section 6 is the general
positive-extension proof. The finite receipt does not replace it.
