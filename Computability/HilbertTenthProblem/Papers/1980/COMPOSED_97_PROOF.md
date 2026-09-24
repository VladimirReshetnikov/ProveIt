# A universal certificate with 97 operations

The unit-centered coefficient construction and the relaxed auxiliary
Pell norm compose. The resulting system has 34 positive unknowns,
22 equations, and an addition/multiplication certificate of length
97 = 54 multiplications + 43 additions. Fixed numerals and equality
tests are free. The supplied parameters are (x,V,H,Tindex), with three
fixed index components besides the queried positive integer x.

The full standalone checker is
`../verification/round29_1980_composed_certificate.py`. It checks both
orders of the complete arithmetic and source-equation transformations.
Their disjointness alone does not prove the mathematical composition;
the proof below checks their common hypotheses and positive witnesses.

## The represented system and its rebuilt index

Apply `UNIT_CENTER_ENCODING_PROOF.md` to any finite Diophantine
representation of the recursively enumerable set in question. Compile
it into nonnegative primitive circuit coordinates with distinct
operands and fresh outputs. Homogenize with delta. Pair multiplication,
addition, copy, zero and final equality rows F with their negatives;
their targets are 2F+delta^2. For each unit coordinate X introduce X',
include the paired copy (X-X')delta and the two unpaired unit rows

    X*delta-delta^2,       X*delta-X*X'.

Place the special target delta^2 first and include the direct guard

    2u*delta-x^2+delta^2.

In particular the guard uses the actual input square, independent of
any copy. Every target's divided quadratic coefficient lies in
{-1,0,1}.

With m positive-weight coordinates, s targets, and input at weight
zero, set

    v_i=3^i (0<=i<m), delta at v_0=1, M=3^(m-1),
    d_0=4M+1, t_j=(s+1)d_0+2M+j*d_0 (0<=j<s),
    t_last=2s*d_0+2M, K_0=t_last+1, c_*=m+s+1.

Include a dummy coordinate at every t_j. The complementary polynomial
D_code(T) has [T^t_j]D_code(T)C(T)^2 equal to the prescribed target.
Use the complete new coordinate and target list to form

    ell_0(T)=sum_i T^v_i+sum_j T^t_j,
    e_0(T)=sum_(0<=j<K_0) T^j+D_code(T).

Choose a power of two L>3K_0+2 and a power of two

    H>max(2*4^(2L+1),4^(t_last+3)*4*c_*^2,3L,16),
    V=ell_0(4)+e_0(4)*4^L, Tindex=psi_4(L).

These three integers are fixed before x is queried. The digits of
e_0 are in {0,1,2}, with unit digit one. The underlying L is not an
additional supplied parameter. The support separation and absence of
an incoming carry at the first special target are proved by the
unit-center construction for this entire new index.

## Combined equations and proof order before decoding

Retain all equations of the 99-operation composition except the
following changes. Put B=Hb^2, theta=B-4, C=x+g and set

    Omega=lambda-e>0,
    sigma=theta*lambda*q-Omega*C^2>0.

Use this sigma throughout the packed equation. In the Pell block put
A=a+4, D_Pell=A^2-1 and replace the auxiliary norm by

    (i*c^2)^2=D_Pell*(f^2-1).                    (1)

The signed norm continues to use K_aux=D_Pell*(f^2-1), which by (1)
is the existing square (i*c^2)^2. The fixed index equation remains
kappa=Tindex+Delta*a. Every other source equation is unchanged.

The unit-center preliminary argument uses positivity, the retained
bound ell+e*q+alpha=q^2, and the geometric equation. Before any Pell
auxiliary equation or internal target is used, it gives

    e<q, ell<q^2, B<=q^2, q>4b>=8, 3L<=B<=n,
    C^2<theta*lambda*q<3q^3<q^4, n=q^8.

With S=g+q^2*(ell+e*q+q^2*sigma) and

    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1),

the width-(2,2,4) packing bounds therefore give

    0<S<n, 0<Tplus<=n, n<=r<=2n^3-2n^2<2n^3.   (2)

Set U=w*n^2, Y=s*n^2, a=Y*(U+1), P=2UY^2+1,
and J=2r+1. Thus U,Y>=n^2, UY>r+1, a>n^4>J,
and the positive interval and first index equation give c>J.

The unchanged main and triangular norms classify c=psi_A(p) and
k=psi_P(t) for positive p,t. The congruence k=r+1 modulo UY implies
t>=r+1, without knowing the main index. Since P>A and c>Yk>k,
Pell growth gives p>=r+2>=66. Consequently

    c>A*D_Pell^2.                               (3)

This is exactly the independent size hypothesis used by
`PELL_RELAXED_AUXILIARY_PROOF.md`. Its integer-coefficient fundamental
unit and strong-divisibility argument applies to (1) and (3), giving
an auxiliary index m_aux with

    f=chi_A(m_aux), p|m_aux, c|m_aux,
    i*c^2=D_Pell*psi_A(m_aux).                   (4)

That argument does not depend on the coefficient baseline, exact q,
any decoded circuit equation, or the signed auxiliary norm. It also
does not assert the stronger old c^2 divisibility of psi_A(m_aux).

Now K_aux=(i*c^2)^2 gives 2K_aux-1=-1 modulo c. By (4), the doubled
signed-index proof has all its hypotheses, including
0<2p<=c<=m_aux. It gives J=+/-p modulo c. Both indices are between
zero and c; the parity psi_A(p)=p modulo 2 excludes J+p=c because J
is odd. Hence p=J and the main coordinates are exactly

    c=psi_A(J), d=chi_A(J).

The subsequent common-witness argument is unchanged. It recovers
the exact first index, proves Y>=U^r and a>U^(r+1), and then gives
U=4^J. The fixed value Tindex=psi_4(L), reduced modulo a, determines
the second Pell index as L; its exponent comparison gives q=B^L.
All growth hypotheses follow from (2) and 3L<=B<=n<=r. The upper
ratio bound and binomial fractional-part estimate give

    b,B,q powers of two,       n^2 | binom(2r,r). (5)

These statements precede coefficient decoding.

## Decode the unit-centered code

The stronger post-Pell bounds now hold:

    lambda>=B^(2L-1)>=Bq>2q, q>=B^2>2B,
    Omega=lambda-e>lambda/2,
    C^2<2theta*q<2Bq<q^2.

Thus g<C<q. The first two masks remove the preliminary borrow and
recover the canonical combined code, up to the quotient alias.
They also bound every coordinate by b. Before delta is identified,
x>0 and g>0 imply C(1)>=2. Writing A_C=C(1)^2, the high plateau of
lambda*C^2 has height A_C, and the high-mask digits of
(B-4)*a_alias are bounded by A_C+4<=4A_C. The displayed H bound and
evaluation at four force that alias to vanish, exactly as in the
unit-center proof.

Both codes are now canonical. The first special target has zero
incoming carry and gives delta in {0,1}; the direct guard rules out
zero before any copies are used. At delta=1, paired rows force F=0,
unit copies agree, and the two unit rows force X=1. All original
circuit equations hold at the actual input x. This proves sufficiency.

## Necessity and every positive witness

Given a solution of the represented system, assign its circuit
coordinates, delta=1, unit copies X'=X=1, and zero dummy digits.
Set u=ceil(x^2/2), so the guard target is one or two. Choose a power
of two b larger than all coordinates and use the canonical codes,
B=Hb^2, q=B^L and n=q^8. The unit-center necessity proof supplies
all positive coding witnesses, the three masks, (2), and (5).

For this newly determined r, construct the full doubled-index Pell
witnesses as in `COMPOSED_99_PROOF.md`: choose U=4^J,
Y=floor((U+1)^(2r)/U^r), a=Y*(U+1), the main and first Pell values,
the positive interval witnesses, the second values at L, and the
positive exponential quotients. The index uses the new fixed
Tindex=psi_4(L). Choose auxiliary m_aux=2cJ and

    f=chi_A(m_aux), i_old=psi_A(m_aux)/c^2>0.

The doubled-index proof constructs positive o and j for its signed
norm. Finally replace only

    i=i_new=D_Pell*i_old>0.

Then (i*c^2)^2=D_Pell*(f^2-1), while the mathematical value K_aux,
and therefore f,o,j and the signed equation, remain unchanged.
The variable i occurs nowhere else. All 34 required unknowns are
positive integers. This proves necessity for the new fixed index.

## Complete arithmetic certificate

The unit-centered encoding saves one addition from 99; the relaxed
auxiliary norm saves one multiplication from the same certificate.
The resulting schedule has 54 multiplications and 43 additions.
The checker verifies that both orders produce precisely the same
97-instruction list and the same 22 source residuals. Relative to
99, only the packed equation, the auxiliary norm, and the positive
sigma and Omega equations change.

There are three acyclic residual corrections: the geometric equation
uses the independently exact theta+4=B equation; the second exponent
uses that same equation; and the signed norm has correction

    -F16*(K_source+K_calculated-1)*(J+jc)^2,

where F16=(i*c^2)^2-D_Pell*(f^2-1) is checked exactly. Subtractions
in the displayed schedule are each represented by a single reversed
addition equation with a free integer intermediate. Thus the claimed
97 is the full addition/multiplication certificate size for the
proved positive-domain system. It is an upper bound, not an
optimality result.
