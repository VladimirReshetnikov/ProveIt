# Simultaneous quadratic coefficient extraction

Let r_1,...,r_m be integral polynomials of degree at most two in n variables.
Their coefficients may depend on fixed integer ports. Let positive weights
w_1,...,w_n, together with the padding weight0, have distinct two-multiset
sums. Put W=max w_i, h=2W+1 and H_j=jh for1<=j<=m.
Write r_j(X)=sum_{|alpha|<=2} p_{j,alpha} X^alpha and set
c_{j,alpha}=(2-|alpha|)! product_i alpha_i! p_{j,alpha}.
Define the ordinary polynomial
D(t)=sum_j sum_alpha c_{j,alpha} t^(H_j-alpha.w).
All exponents are nonnegative. The individual row blocks occupy disjoint
intervals [H_j-2W,H_j]. Within each block, pair-sum uniqueness makes all
monomial positions distinct. Thus every coefficient of D has magnitude at
most M=max|c_{j,alpha}|, without an additional factor m.

For C(t)=(1+sum_i x_i t^w_i)^2, coefficient extraction gives
[t^H_j] C(t)D(t)=2r_j(x).
To verify this, a contribution from row k would require
H_j-H_k=beta.w-alpha.w, where both alpha and beta have total degree at most2.
The right side belongs to[-2W,2W], whereas every nonzero target difference
has magnitude at least2W+1. Therefore k=j. Pair-sum uniqueness then forces
alpha=beta, and the factorials cancel the multinomial coefficient.

This is stronger than first replacing the system by a quartic sum of
squares: each residual is extracted separately, and all equality tests can
share one no-carry test. If B is a power of two and each coefficient a_i of
A(t)=C(t)D(t)+(B/2) sum_{i=0}^{H_m+2W}t^i is strictly between0 andB, then

  tau_2(2 A(B), (B-2) sum_j B^H_j)=0
  iff tau_2(A(B), (B/2-1) sum_j B^H_j)=0
  iff a_(H_j)=B/2 for every j
  iff r_j(x)=0 for every j.

Here tau_2 denotes the number of binary carries. Every target mask lies
in a distinct base-B cell. No carry means bitwise disjointness, so the
simultaneous test is exactly the conjunction of the individual cell tests.
The doubling step divides both addends by2; it simply shifts binary bits.
No carry-free claim about the unhalved coefficient expression is needed.

If 0<=x_i<b then every coefficient of C D has absolute value at most
M(1+sum_i x_i)^2 <=M(nb)^2. Choosing B>4M(n+1)^2 b^2 gives the needed
strict digit bounds. Off-target coefficients of different row products
may overlap; the stated bound is still valid because it bounds the
convolution using the coefficient bound for the entire D and the sum of
all nonnegative coefficients of C.

For the positivity required by the arithmetic compiler, reorder and, if
necessary, negate a row so that the final row has r_m(0)>0. Then the leading
coefficient of D is2r_m(0)>0 at degree H_m; all other terms have lower
degree. For B>M+1, the absolute sum of the lower terms at B is less than
B^H_m. Consequently D(B)>0. The same row guarantees that the all-zero
source vector is not a solution. These facts supply the two properties
previously obtained from a positive constant term of a sum of squares.

The rest of the direct source adapter must establish its own size bounds,
cofinal choice of b, and the central-binomial/Pell interface. This lemma
establishes the multiple-output replacement independently of those steps.

