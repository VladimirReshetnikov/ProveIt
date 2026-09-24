# Short masks: a 118-operation successor to the packed certificate

This construction changes the admissible index once more. It does not
claim pointwise equivalence for old indices or old witness tuples. Its
exact schedule is `../verification/round5_1980_short_masks.py`; the
independent symbolic check passes with 118 instructions: 65 multiplications
and 53 additions, twenty equations and 32 positive unknowns. A further
independent Pell-polynomial improvement may be composed with it separately.

## A quartic encoding with zero leading coefficient code

Start from the quadratic-system representation behind the known quartic
universal pair with 58 existential variables. After shifting its positive
witnesses to nonnegative coordinates, write the quadratic residuals as
`F_i(X,z_1,...,z_58)`. Their coefficients, including their constant terms
`c_i`, are fixed for the represented recursively enumerable set.

Introduce a new nonnegative variable h and put

    F_i^h = F_i-c_i+c_i*h,
    S = sum_i (F_i^h)^2 + (X*h-X)^2.

This has degree at most four, is a sum of squares, and has zero constant
coefficient. For X>0, S=0 forces h=1, and is therefore equivalent to the
original quadratic system. Introduce another nonnegative variable sigma.
Choose a power of two z>=4, sufficiently large as specified below, and
use the quartic polynomial

    R = 24*S + z*(sigma-1).

For nonnegative integral witnesses, R=0 is equivalent to S=0 and sigma=1.
Indeed, sigma>=2 makes R positive, sigma=1 gives S=0, and sigma=0 would
require `24*S=z`, impossible because 3 does not divide a power of two.
Thus this representation remains universal for positive X. The condition
sigma=1 also ensures its actual witness code g is positive.

There are now nu=60 existential coefficient-encoding variables. Let

    c_i = 4!/(i_0! ... i_nu! (4-sum i_j)!),

for all multiindices of total degree at most four. Every c_i divides 24.
Write directly

    R = sum_i c_i*P_i * X^i_0 z_1^i_1 ... z_nu^i_nu.

All P_i are integers: the S contribution is multiplied by 24, and the
linear sigma coefficient has weight 4, so its P_i is z/4. The constant
weight is 1 and `P_0=-z`. Choose z so large that every P_i arising from
24*S has absolute value less than z; this is possible because S was fixed
before choosing z. The fresh sigma variable does not occur in S, so its
coefficient z/4 cannot interfere with this choice. Consequently

    P_0=-z,       -z<P_i<z for i!=0.

This direct weighted-coefficient convention is essential: the target
coefficient will be R itself, rather than 24 times R. Its integer
coefficients already have the necessary multinomial divisibility.

Set Z=2z, `M=5^nu`, and `L=5^64=625*M`. For a multiindex i write
`w(i)=i_0+i_1*5+...+i_nu*5^nu`. The bound `w(i)<=4M<L` holds.
Define the digit polynomials

    l_0(B) = sum_{j=1}^nu B^(5^j),
    e_0(B) = sum_i (z+P_i)*B^(L-w(i)).

The term i=0 vanishes because z+P_0=0. Thus e_0 has degree at most L-1;
all its nonzero digits lie in [0,Z), and its highest possible coefficient
is positive (for example the linear-X coefficient of S is zero). There
are no collisions between distinct multiindices, by uniqueness of base-5
digits with digits at most four.

The packed parameter is

    V = e_0(Z) + l_0(Z)*Z^L.

Choose a power of two H satisfying

    H > max(2*Z^(2L+1), Z*(nu+2)^4, 3L, 64).

An index (Z,V,H) is admissible if constructed by these rules from a
quadratic-system representation. Index construction is external to the
straight-line certificate, just as in the preceding packed construction;
V and H are fixed parameters, not freely chosen existential witnesses.
The complete parameter list remains `(x,Z,V,H)`.

## The new polynomial system

Keep the 32 positive unknowns of the 120-operation packed system and
write `B=H*b^4`, `C=1+x*B+g` as charged abbreviations. Replace its bound,
geometric equation, packed congruence, and n equation by

    b=x+beta,
    e+l*C^4+alpha=q,
    lambda+q^2=1+lambda*B,
    theta+Z=B,
    e+l*q=V+t*theta,
    n=q^8.

The positivity witnesses beta and alpha are retained. Use the new fixed
exponent L in the same Pell exponent-replacement equations, with base B.
All the remaining Pell equations and the flat gap `c=kappa+phi` remain
unchanged. The packing equation is

    S3=(2e-Z*lambda)*C^4+B*lambda*(1+q^2),
    S=g+q*(e+l*q+q^2*S3),
    Tplus=q-(b-1)*l+theta*lambda*q+(B-2)*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).

Here S, S3 and Tplus are abbreviations computed by the certificate.
There remain twenty equations.

## Bounds established before the exponential equation

Assume the polynomial system has a positive-integer solution. From the
new bound,

    e<q, l<q, C^4<q.

Since C>B>b>=2, one has q>B and g<q. In fact `l*C^4<q` gives
`(b-1)*l<q`, so the first mask

    T1=q-1-(b-1)*l

is nonnegative and less than q. The geometric equation implies
`lambda=(q^2-1)/(B-1)>q`; hence, with z=Z/2 at the metalevel,

    0<D0=z*lambda-e<z*lambda.

As C^4<q and B>2z, the third block satisfies

    2*C^4*D0 < 2z*lambda*q < B*lambda*q,
    0<S3<B*lambda*(1+q^2)
         =B*(q^4-1)/(B-1)<2q^4<q^5.

The other blocks satisfy

    0<S1=g<q,
    0<=T1<q,
    0<S2=e+l*q<q^2,
    0<T2=(B-Z)*lambda<(B-1)*lambda=q^2-1,
    0<T3=(B-2)*q<q^2<q^5.

Thus the widths may be `N1=q`, `N2=q^2`, `N3=q^5`, giving
`n=N1*N2*N3=q^8`. The packing equation has precisely these S,T blocks,
with `Tplus=T+1`; it implies `r>=n^2-1>=n`. Admissibility gives

    3<3L<=B<q<=n<=r.

The same elementary Pell gap restores the stronger c inequality needed
by Lemma 2.26. Lemmas 2.25 and 2.26 therefore yield b a power of two,
`q=B^L`, and the central-binomial divisibility simultaneously. No power-of-two
or exponent conclusion was assumed when establishing these bounds.

## Decoding and the zero-coefficient test

Now B and q are powers of two. Lemmas 2.16 and 2.11 recover the three
separate no-carry conditions. Apply Lemma 2.9 with digit base Z,
`Y=e+l*q`, and `m=k=2L`. The packed polynomial

    F(B)=e_0(B)+l_0(B)*B^L

has degree at most L+M<2L, digits in [0,Z), disjoint lower and upper
blocks, and F(Z)=V. The new congruence, `Y<q^2=B^(2L)`, the mask
`(B-Z)*lambda`, and `B>2Z^(2L+1)` satisfy the lemma's hypotheses.
Therefore Y=F(B). Both supplied e,l and intended e_0,l_0 lie in [0,q),
so quotient-and-remainder uniqueness gives `e=e_0(B)`, `l=l_0(B)`.

The first mask then ensures g has nonzero digits only in the positions
5^j, and all these digits are less than b. Thus C encodes x and a
tuple of nonnegative witnesses bounded by b.

Regard B temporarily as a formal base. The coefficient of B^L in

    C^4*(e_0(B)-z*lambda)

is exactly R evaluated at that tuple. For each monomial exponent w(i)
of C^4, the complementary e digit is z+P_i, including the zero digit
at i=0; subtracting z*lambda leaves P_i in every such complementary
position. The multinomial coefficients of C^4 are exactly the c_i.
There is therefore no missing leading-digit correction: `P_0=-z` is
the reason the removed leading digit is legitimate.

Every coefficient of `e_0-z*lambda` has absolute value at most z. Since
the sum of the coefficients of C^4 is `(1+x+sum witness_j)^4`, every
coefficient of their product has absolute value less than

    z*((nu+2)*b)^4 < B/2.

Its degree is at most `2L-1+4M<3L`. The added offset
`(B/2)*lambda*(1+q^2)` supplies B/2 in every position below 4L.
Consequently the third no-carry condition, after dividing its two
arguments by two, tests the digit in position L against B/2-1; by
Lemma 2.8 it holds exactly when R=0. The normalization proved above
then gives membership in the represented recursively enumerable set.

## Necessity and positivity of the new bound

For an actual solution of the original quadratic system choose h=1,
sigma=1, and a power-of-two b greater than x and all sixty witnesses.
Use B=H*b^4, q=B^L and the intended codes. Their estimates are

    e_0(B)<Z*B^(L-1),
    l_0(B)<2*B^M,
    C<2*b*B^M.

The first follows from the digit bound Z<B and degree at most L-1.
Since B>2Z, it gives e<q/2. Also

    l*C^4 < 32*b^4*B^(5M)
            < (1/2)*B^(5M+1) <= q/2,

using H>64 and L=625M>=5M+1. Thus `e+l*C^4<q`, giving positive
alpha. The fixed digit polynomial F has positive degree and B>Z, so
`t=(F(B)-F(Z))/(B-Z)` is a positive integer. Its g is positive
because sigma=1. The remaining witnesses are obtained from the same
no-carry and Pell necessity constructions, with the new base and exponent.

## Instruction count

Relative to the 120-operation schedule, the new bound replaces
`el`, `(el)*C^2`, and addition of alpha by `l*C^4`, addition of e,
and addition of alpha. The count stays three, with one fewer
multiplication and one more addition. All packing computations have the
same number of instructions after changing their exponents. However,
only q^2, q^4 and q^8 need be built; q^3 and q^16 disappear. The
total is therefore 118, with 65 multiplications and 53 additions.
The exact E7 residual identity becomes

    F7_new = F7_old + (lambda*F3-F2)*q*(n^2-1),

and is checked symbolically along with all other residuals. This is a
proved upper bound; no optimality claim is intended.

The length L was deliberately chosen as 5^64 rather than the smallest
integer allowed by these bounds. It exceeds 4M and 5M+1, keeps the
packed-code degree L+M below 2L and the product degree 2L-1+4M below
3L, and costs only six squarings after generating 5. Thus generating
the fixed literals 2,4,5,L takes nine instructions in total: three
additions for 2,4,5 and six multiplications for 5^2,5^4,...,5^64.
The supplied index parameters x,Z,V,H are not generated by those nine
instructions. Composing the subsequently verified 114-operation system
with this chain gives 123 operations under that stricter convention.
