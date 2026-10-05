# A sharp dilation improvement for integer matrices in Markov masks

Any finite family of integer r-by-r matrices embeds into strictly positive
normalized trigonometric Markov masks with dilation **r+1** and degree at most
**r²+r−1**. The earlier lift used dilation2r+1 and degree2r²+r−1. The new
construction uses real sine coordinates and deliberately allows the two
complex Fourier blocks to interact. This interaction removes the old
frequency-separation overhead. The new dilation is the smallest possible
for transporting arbitrary matrices in the standard consecutive sine
coordinates, even if the alternative masks are not even.

These are sharper representation bounds, not an improved universal
Diophantine operation count. Matrix evolution, input binding, integer
normalization, admissible words and fixed-arity histories remain charged.

## 1. Exact construction

Use the same finite source identity as `markov_mask_matrix_lift.md`:

    T_a e_m = sum_(b divides m+j) a_j e_((m+j)/b),
    (T_a f)(x) = (1/b) sum_(ell=0)^(b-1)
                   a((x+ell)/b) f((x+ell)/b).

Here e_m(x)=exp(2*pi*i*m*x), the mask Fourier coefficient is a_j, and
normalization is a_0=1 and a_(b*j)=0 for every nonzero integer j. For a real
even mask, the coefficient of sin(2*pi*k*x) in the image of
sin(2*pi*m*x), for k,m>0, is

    a_(bk−m) − a_(bk+m).                                      (1)

The constant contributions cancel. This difference, rather than the
positive-character block alone, is the useful coordinate map.

Given M, put b=r+1 and define the involution J(m)=b−m on{1,...,r}. Recursively
from the last row upwards set

    C_(r+1,m)=0,
    C_(k,m)=M_(k,m)+C_(k+1,J(m))       (k=r,...,1).              (2)

For a finite nonempty family M_sigma compute C_sigma this way and set

    S=max_sigma sum_(k,m=1)^r |C_sigma[k,m]|,
    q=2S+1,
    a_sigma(x)=1+(2/q) sum_(k,m=1)^r
                         C_sigma[k,m] cos(2*pi*(bk−m)*x).      (3)

The positive frequencies bk−m are distinct and are exactly the integers
between1 and br−1 that are not multiples of b. Indeed each row lists the
r=b−1 integers strictly between b(k−1) and bk. Thus (3) is normalized,
has integer Fourier numerators and common denominator q, and has degree
at most br−1=r²+r−1. Also

    a_sigma(x) >= 1−2S/q = 1/q > 0.                           (4)

The zero family has q=1 and constant mask1.

The two coefficients in (1) are C_(k,m)/q and C_(k+1,J(m))/q, since
bk+m=b(k+1)−J(m). The latter is zero in the last row. Equation(2) therefore
gives the exact block identity

    T_(a_sigma) g_v = g_(M_sigma v/q),
    g_v(x)=sum_(m=1)^r v_m sin(2*pi*m*x).                      (5)

No frequency outside the r-core occurs: for |m|<=r and |j|<=br−1,
|(m+j)/b|<r+1. The constant image cancels between the two input characters.
Unlike the earlier construction, the positive and negative complex
characters need not be separately invariant. Only the real sine block is
being specified. The cosine block is generally a different matrix and can
leak into constants; this does not affect (5). Constants themselves remain
fixed by every mask.

The coefficient growth is explicit:

    C_(k,m)=sum_(ell=0)^(r−k) M_(k+ell,J^ell(m)),
    sum|C| <= sum_(j=1)^r j*sum_m|M_(j,m)| <= r*sum|M|.        (6)

Thus the smaller dilation/degree can require a larger denominator under
the simple absolute-sum positivity certificate. It is not uniformly a
smaller-coefficient representation.

## 2. Sharpness and uniqueness in the stated coordinates

**Minimum dilation for arbitrary matrix transport.** Every normalized
Markov operator satisfies

    T_a sin(2*pi*b*x) = sin(2*pi*x),                          (7)

because its pullback factor is sin(2*pi*(x+ell)) and T_a 1=1. If2<=b<=r,
the b-th sine coordinate lies in the proposed r-coordinate block. Equation(7)
prevents the identity matrix divided by any nonzero scalar from being that
block: its b-th column would have to send the b-th sine to a multiple of
itself, whereas (7) sends it to the first sine. Therefore b>=r+1 is necessary
for a representation of every matrix, or even for a family containing the
identity, in this fixed standard basis. For r=1 the allowed integer dilation
already starts at2=r+1. This obstruction does not require evenness or finite
support. It does not exclude smaller dilation after changing the encoding,
using different frequencies, or restricting the matrix family.

**Uniqueness of the finite even lift at b=r+1.** Suppose a finite real even
normalized mask preserves the standard r-sine block. If N is its largest
positive nonzero Fourier frequency, normalization makes N nondivisible by
b. Let m=b−(N mod b), so1<=m<=r. For k=(N+m)/b, the coefficient in (1) is
a_N−a_(N+2m)=a_N. If N>br−1 then k>r, contradicting invariance. Consequently
every such mask has degree at most br−1.

All its remaining free positive coefficients can therefore be written
c_(k,m)=a_(bk−m). The sine matrix is exactly
c_(k,m)−c_(k+1,J(m)), with the last-row successor zero. This triangular map
is invertible. For a prescribed matrix M/q its unique solution is C/q from
(2). In particular arbitrary extra finite high frequencies cannot improve
positivity while keeping the same block in this even-mask class.

The worst-case degree bound is sharp in that class. A matrix with
M_(r,1)!=0 forces a_(br−1)=M_(r,1)/q, so its mask really has degree br−1.
This is a statement about this coordinate interface, not a lower bound on
the dimension or degree of all possible functional encodings.

## 3. An exact small-scale counter example

For the two homogeneous-coordinate matrices

    I = [[1, 0], [0, 1]],
    D = [[1,-1], [0, 1]],

formula(2) gives C_I=[[2,0],[0,1]] and C_D=[[2,-1],[0,1]]. The general
absolute-sum rule would choose q=9. In this particular family, **q=5** is
already strictly positive, with dilation3 and degree4:

    a_I = 1+(4 cos(2 theta)+2 cos(4 theta))/5,
    a_D = 1+(4 cos(2 theta)−2 cos(theta)+2 cos(4 theta))/5,
    theta=2*pi*x.

Put t=cos(theta) in[−1,1]. Their numerators at denominator5 are

    5 a_I = (4t²−1)²+2,
    5 a_D = (4t²−1)²+2(1−t).                                 (8)

The second is at least1/2: for t<=3/4 the second summand is at least1/2;
for t>=3/4 the square is at least25/16. Hence both masks are strictly
positive and a_D>=1/10. The largest frequency4 is below the generic degree5
bound because M_(2,1)=0 in both matrices.

The integer denominator5 is minimal for these fixed matrices in this
even, dilation3, standard-sine encoding. At q=4 and t=3/5, the decrement
mask numerator equals−4/625. Reducing a positive integer q further only
reduces that numerator. The uniqueness statement above excludes adding
other even finite Fourier coefficients while preserving D/q. This is not
a global minimum over other encodings or noninteger normalizations.

## 4. Arithmetic and computational scope

For a word of length T, (5) gives exactly

    T_(a_sigma_T)...T_(a_sigma_1) g_v
       = q^(−T) g_(M_sigma_T...M_sigma_1 v).

Zero-vector and homogeneous polynomial zero tests transfer; nonzero targets
still need their duration scale. Whole-operator mortality remains impossible
because every operator fixes1. No claim of a new universal matrix system is
made. The two matrices above illustrate a guarded counter coordinate, not
a complete universal counter program or an unbounded integer-history graph.

With the matrix selected and its entries supplied, direct integer evolution
still has the sufficient r²M+r(r−1)A bound from the earlier note. The finite
triangular coefficient transform has r(r−1) additions, computed once for
each fixed matrix; compiling the positivity scale also requires bounding
its coefficients. These are mask-construction costs, not free variable
operations in a universal polynomial. Fourier support has at most2r²+1
entries. Smaller dilation and polynomial degree do not by themselves lower
the number of ordinary additions/multiplications required for a history.

## 5. Evidence and inherited scope

The preceding lift note was read in full, SHA256
`5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6`;
its independent review has SHA256
`4b371b8edc261c8cd6cc4bbd3e86c2b0133bfbf715365d6726c1292face8214c`.
The literal Fourier interface comes from lines368–423 of
`holder_zygmund_spectra/holder_zygmund_spectra.tex`, SHA256
`98bc2920135319f1d9b72b14c180112fdbae39971d2cdd9698e3dc4aed4b63da`,
in the archive at e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9, archive SHA256
`13ff104b4e3df02b1cd419318a4698e490911460935195cd40da18edfd2983c6`.
Only that already reviewed finite interface is inherited, not the report's
infinite-dimensional spectrum theorems.

The new helper checks28 masks in dimensions1–7,112 sine basis images,
448 two-step images, separate wholly zero families and the exact q=5
counter matrices. Exact rational Chebyshev coefficients check (8) and the
q=4 counterexample; the all-size/sharpness proofs are the arguments above.
Fresh writer, normal and optimized runs from `/` passed before freeze.
No archived, supplied, committed or frozen helper or source array was
executed or imported. No universal operation bound is changed.
