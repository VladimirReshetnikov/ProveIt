# Direct quadratic equations with a shared mask: 113 instructions

The predecessor has a verified 114-operation certificate. This successor
encodes the original quadratic residuals individually, using their common
mask also as the witness-position mask. It therefore replaces C^4 by C^2
and B=H*b^4 by B=H*b^2. The changed target mask costs one multiplication,
so the net improvement is one operation.

The companion `../verification/round6_1980_quadratic_certificate.py`
verifies all source residuals, both triangular identities, the complete
addition/multiplication instruction list, the histogram, and the uniform
integer support inequalities below. It passes with 113 instructions:
62 multiplications and 51 additions. There remain 33 positive unknowns,
21 equations, and the four parameters x,Z,V,H. Generating the fixed
literals 2,4,5,L from 1 costs seven more instructions, giving 120; the
four parameters remain supplied under that convention.

## A fixed number of quadratic residuals

Use the quadratic-system construction underlying the universal pair
(58,4) in section 5 of the corrected Jones paper. For a fixed represented
recursively enumerable set, shift the positive witnesses to nonnegative
coordinates and write its quadratic residuals as

    F_r(X,z_1,...,z_58).

There are 59 polynomial coordinates including X, so the vector space over
Q of polynomials of degree at most two has dimension

    J = binomial(61,2) = 1830.

Select a maximal Q-linearly independent subset of the coefficient rows of
the residuals. Vanishing of this subset is equivalent to vanishing of
all the residuals, because every discarded row is a rational linear
combination of the retained ones. The selected polynomials still have
integer coefficients, since they are selected from the original list;
alternatively a row-reduced rational basis may be multiplied by its
denominators. Pad the list with zero residuals to exactly J rows. This
preprocessing is computable and depends only on the represented set.

## Fixed supports and exact spacing

Put A=2*58^2+1=6729. Give the input and 58 witness coordinates weights

    v_i=1+3*(A*i+i^2),       0<=i<=58.

The input weight is v_0=1 and v_max=v_58=1180939. These weights are
all 1 modulo 3, so monomials of degrees zero, one and two have distinct
weight residues modulo 3. Within degree two, equality of pair sums
recovers i+j and i^2+j^2 separately: after removing the common 2 and
dividing by 3, division by A has quotient i+j and remainder i^2+j^2,
because 0<=i^2+j^2<=2*58^2<A. The sum and sum of squares determine
the unordered pair {i,j}. Degree-one weights are strictly increasing.
Thus every monomial of total degree at most two has a distinct weight
w(I), and w(I)<=2*v_max. This is also checked by enumerating the exact
1830 weights, including the constant monomial.
Let c_I denote its multinomial coefficient in a square, with the unused
degree supplied by the constant coordinate 1. Thus c_I is either 1 or 2.

Define the following fixed integers:

    J=1830,
    d=4*v_max+1,
    t_first=(J+1)*d+2*v_max,
    t_r=t_first+r*d       (0<=r<J),
    t_last=t_first+(J-1)*d,
    L=5^16=152587890625.

They satisfy

    d>2*v_max,
    t_first-2*v_max>v_max,
    2*t_first-2*v_max>t_last,
    L>3*t_last+1.

The checker verifies these inequalities as exact integer statements, not
floating-point estimates. The intervals [t_r-2*v_max,t_r] are disjoint.
Here t_last=17291312498 and 3*t_last+1=51873937495<L.
Moreover, multiplying a polynomial supported in these intervals by a
code coordinate of weight at least t_first cannot contribute to any
position at most t_last.

The mask is the fixed support polynomial

    ell_0(B)=sum_{i=1}^58 B^(v_i) + sum_{r=0}^{J-1} B^(t_r).

It has coefficient 1 at each support position. Its first 58 positions
hold the actual witnesses; its other J positions may hold dummy code
coordinates. In total there are 1888 code coordinates. These are encoded
digits of the single positive variable g, not 1888 additional unknowns
in the final system.

## Encoding the coefficient data

For row r and monomial I define

    a_(r,I) = 2*coefficient(F_r,I)/c_I.

These are integers because c_I divides 2. Let

    D(B)=sum_(r,I) a_(r,I)*B^(t_r-w(I)).

No distinct summands can collide: monomial weights are unique within
each row, and the row support intervals are disjoint. Choose a power
of two z>=2 greater than every |a_(r,I)|, and put Z=2z. The coefficient
code is deliberately dense:

    e_0(B)=z*sum_{j=0}^{L-1} B^j + D(B).

Every digit of e_0 lies in [0,Z), in fact between 1 and Z-1. Its degree
is L-1. This dense baseline is essential: below L, subtracting the
geometric baseline z leaves exactly D, including zero coefficients at
all the low variable positions.

The packed index is

    V=e_0(Z)+ell_0(Z)*Z^L.

Choose a power of two H satisfying

    H>max(2*Z^(2L+1), Z*1890^2, 3L, 16).

An admissible index is a triple (Z,V,H) produced by this construction.
Its definition, including the rational row-basis reduction and the
coefficient scaling, is fixed independently of the input x. V,H are
fixed parameters of the represented set, not arbitrary existential
witnesses selected by a purported certificate.

## The final system

Retain the 33 positive unknowns, the signed Pell parameter, and the
linear ratio equations of the verified 114-operation system. Write

    B=H*b^2,       C=1+x*B+g.

Replace the coding bound and the r equation by

    b=x+beta,
    e+ell*C^2+alpha=q,
    S3=(2e-Z*lambda)*C^2+B*lambda*(1+q^2),
    S=g+q*(e+ell*q+q^2*S3),
    Tplus=q-(b-1)*ell+theta*lambda*q+(B-2)*ell*q^3,
    r=S*(n^2-n)+Tplus*(n^2-1).

The other coding equations remain

    lambda+q^2=1+lambda*B,
    theta+Z=B,
    e+ell*q=V+t*theta,
    n=q^8.

The exponent lemma continues to use base B and exponent L=5^16.
All B occurrences are changed consistently, including its Pell
congruence. B,C,S,S3,Tplus are charged abbreviations, not free equations.

## Noncircular size bounds

Suppose the polynomial system has a positive-integer solution. From
e+ell*C^2<q and b>x>=1 one has

    e<q, ell<q, C^2<q, C>B>b>=2, q>B, g<q.

The first mask is nonnegative because

    (b-1)*ell < C^2*ell < q,
    0<=T1=q-1-(b-1)*ell<q.

The geometric equation gives lambda>q; hence

    0<D0=z*lambda-e<z*lambda,
    2*C^2*D0<2z*lambda*q<B*lambda*q.

Consequently the three blocks satisfy

    0<S1=g<q,                     0<=T1<q,
    0<S2=e+ell*q<q^2,            0<T2=(B-Z)*lambda<q^2,
    0<S3<B*lambda*(1+q^2)<2q^4<q^5,
    0<T3=(B-2)*ell<C^2*ell<q<q^5.

Their widths q,q^2,q^5 have product n=q^8, and Tplus is exactly T+1
for their packing. Thus r>=n^2-1>=n. The admissible H gives
3<3L<=B<q<=n<=r. The Pell-gap argument and the signed Pell and linear
ratio equivalences remain applicable, because their hypotheses use
these bounds and the otherwise unchanged Pell equations. The Pell
lemmas therefore imply simultaneously that b is a power of two,
q=B^L, and the required central-binomial divisibility holds. This
deduction has not assumed any of those conclusions prematurely.

## Decoding and absence of cross-row contamination

Since H and b are powers of two, B and q are powers of two. The central
binomial criterion and the block-packing lemma give all three no-carry
conditions. Apply Lemma 2.9 with digit base Z, Y=e+ell*q, and m=k=2L.
The packed polynomial

    F(B)=e_0(B)+ell_0(B)*B^L

has degree L+t_last<2L and digits less than Z. Its two parts have
disjoint supports, and F(Z)=V. The supplied congruence, the bound
Y<q^2=B^(2L), the mask (B-Z)*lambda, and B>2Z^(2L+1) prove
Y=F(B). Both supplied and intended e,ell lie in [0,q), so quotient
and remainder uniqueness gives e=e_0(B) and ell=ell_0(B).

The first mask now shows that g has arbitrary digits in [0,b) only
at the support of ell_0, and zero digits elsewhere. Thus its low
coordinates give the actual 58 witnesses, and its high coordinates
give the dummy values. Since b>x, C=1+xB+g has precisely the intended
input digit and these witness digits, with no carry between them.

Below L the coefficient polynomial e_0-z*lambda is exactly D; between
L and 2L-1 it has coefficient -z. The latter tail cannot contribute
to a target below L. For a low target v_i, D has minimum degree
t_first-2*v_max>v_max, so the coefficient of C^2*D at v_i is zero.

For a row target t_s, consider a term of D belonging to row r, at
exponent t_r-w(I), multiplied by a monomial from C^2. If that monomial
uses a dummy coordinate, its exponent is at least t_first, so their
sum is at least 2*t_first-2*v_max>t_last; it cannot reach t_s. For
monomials using only the original coordinates, the exponent is w(J)
with 0<=w(J)<=2*v_max. If r!=s, the row separation d>2*v_max makes

    t_r-w(I)+w(J)=t_s

impossible. If r=s, uniqueness of the quadratic monomial weights forces I=J.
Therefore the coefficient at t_s is exactly

    sum_I c_I * a_(s,I) * monomial_I = 2*F_s.

The dummy code coordinates are consequently harmless for every tested
coefficient, even when they are nonzero. This argument is necessary;
they are not silently assumed to be zero in the soundness direction.

## Why the shared third mask tests precisely the residuals

Every coefficient of e_0-z*lambda has absolute value at most z. There
are 1888 possible witness/dummy digits, each less than b, and x<b.
The sum of coefficients of C^2 is therefore less than (1890*b)^2.
Every coefficient of C^2*(e_0-z*lambda) has absolute value less than

    z*(1890*b)^2 < B/2,

by the chosen bound on H. Its degree is at most 2L-1+2*t_last<3L.
Adding (B/2)*lambda*(1+q^2) supplies B/2 at every position below 4L;
the resulting digits all lie strictly between 0 and B. There are no
carries. Half of the third mask is

    (B/2-1)*ell_0(B).

Its digit is B/2-1 at every low variable position and every row
target, and zero elsewhere. Lemma 2.8 applied at those disjoint base-B
positions says that the third no-carry condition is equivalent to the
vanishing of all the tested coefficients. The low tests are automatic
zeros, and the row tests are precisely 2*F_s=0. The row-basis reduction
then proves membership in the original recursively enumerable set.

## Necessity

Take an actual solution of the original quadratic system. Choose a
power-of-two b exceeding x and its 58 nonnegative witnesses. Set one
dummy code coordinate to 1 and the others to zero; enlarge b if
needed. This ensures g>0 independently of whether the original
witnesses all vanish. Use B=H*b^2, q=B^L and the intended e,ell,g.

The digit estimates give

    e<Z*B^(L-1)<q/2,
    ell<2*B^(t_last),
    C<2*b*B^(t_last).

Hence

    ell*C^2 < 8*b^2*B^(3*t_last)
              < (1/2)*B^(3*t_last+1) < q/2,

using H>16 and the exact checked inequality L>3*t_last+1. Therefore
alpha=q-e-ell*C^2 and beta=b-x are positive. The packed polynomial
has positive degree and nonnegative digits, so F(B)>F(Z), and
t=(F(B)-F(Z))/(B-Z) is positive integral. The mask conditions follow
from the code supports and the row-equation proof above. The remaining
Pell witnesses follow from the same necessity lemmas, with unchanged
strict linear ratio and signed Pell conditions.

## Accounting and exact receipts

Building B=H*b^2 costs two multiplications instead of the former three.
The code power C^2 is already computed, and the separate squaring for
C^4 disappears. The third mask is now (B-2)*ell rather than (B-2)*q.
Its contribution to Tplus is evaluated as

    (B-2) * ((ell*q)*q^2),

reusing ell*q from the second packed block. This costs one additional
multiplication relative to (B-2)*q^4. No standalone q^3 is computed.
Thus the change saves 2-1=1 instruction, giving 113.

The complete verifier checks all twenty-one polynomial residuals and
the two previously established triangular identities. The E7 correction
remains `(lambda*F3-F2)*q*(n^2-1)`, and the signed Pell correction
remains the one from the preceding verified system. Every serialized
primitive is also independently checked as an addition or multiplication
identity. These arithmetic checks complement, rather than replace,
the positive-domain and coefficient-support proof above.
