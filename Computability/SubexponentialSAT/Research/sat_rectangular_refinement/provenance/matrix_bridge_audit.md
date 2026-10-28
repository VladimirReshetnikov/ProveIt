# Audit: current complex matrix-multiplication bounds over the exact mode ring

## Conclusion

The proposed bridge is valid with fixed positive exponent slack and a finite
collection of base bilinear algorithms chosen before the SAT input. It does
not require a new all-characteristic matrix-multiplication theorem. A fixed
number field containing algebraic coefficients of the base identities can be
reduced modulo every odd prime outside a fixed finite set, even when its
defining polynomial becomes reducible or inseparable. Integer-coordinate
lifting and CRT then transfer the algorithms to the two-adic mode ring.

The principal pitfalls are (i) dropping the positive exponent slack;
(ii) treating a theorem for each fixed shape as an algorithm uniform in a
continuously changing input shape; (iii) reducing elements of Z/2^p Z directly
modulo odd primes; and (iv) deriving a space guarantee from the arithmetic
exponent alone without supplying a depth-first bilinear schedule.

This note establishes the mathematical bridge. It does not instantiate the
large finite base algorithms, benchmark them, or locally rebuild any Lean
formalization.

## 1. Current primary source statements

Pinned OpenAI source:

https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/107.md

This documents complex square exponent at most 9/4, dual exponent strictly
above 0.465, and a bound below 2.092 at rectangular ratio 0.709, with arbitrary
positive exponent slack. The comparator statement uses finite division-free
arithmetic programs with complex constants. It is an arithmetic-complexity
statement, not directly a bit-complexity or memory theorem.

The newer rectangular curve is stated in Theorem 1.1 and Corollary 1.2 of

https://arxiv.org/html/2610.10494v2

For a >= b >= c >= 0 its bound is

    G(a,b,c) = a+b,                                c <= ab/(a+b),
             (a+b+c)/2 +(ab/c+ac/b+bc/a)/4,          otherwise.

In particular omega(1,k,1) <= 2 for k <= 1/2, and <= 1+k+1/(4k) for k >= 1/2.
Its convention suppresses positive vanishing exponent slack and fixes the
shape parameters. Section 6, Lemma 6.1, explicitly derives a fixed finite exact
rank decomposition for each fixed shape and slack, then recurses on it.
The paper works over C and states extension to characteristic zero.

The narrower source-backed choice alpha_0=23/50 is enough for an improved
conservative certificate. The choice alpha_0=1/2 additionally uses the newer
rectangular theorem. These two provenance levels should be distinguished.

## 2. Algebraic descent of a finite complex bilinear identity

Fix integer matrix dimensions (a,b,c), a rank r, and an exact complex tensor
decomposition of their multiplication tensor:

    T = sum_{t=1}^r u_t tensor v_t tensor w_t.

The finitely many coefficient equations for this decomposition are polynomial
equations over Q: each entry of T is zero or one. If they have a solution over
C, their ideal remains proper over the algebraic closure of Q. The weak
Nullstellensatz over that algebraically closed field supplies a solution with
all coefficients algebraic over Q. Hence the same rank is attainable using
coefficients in one finite number field K.

Choose an algebraic integer theta with K=Q(theta), and let g in Z[T] be its
monic minimal polynomial of fixed degree d. Each of the finitely many
algorithm coefficients lies in

    A = Z[1/D,theta] = Z[1/D][T]/(g)

for one fixed positive integer D. Include the coefficients of every algorithm
in the finite library in the same K and D (take their compositum and a common
denominator). All choices here depend on the fixed exponent slack and selected
base identities, not on matrix dimensions encountered in the SAT computation.

The identity is an identity of polynomials over A. To see this without any
integrality assumption on tensor coefficients beyond the common denominator,
reduce each coefficient difference modulo the monic g. Its remainder has
coefficients in Z[1/D] and is zero in Q[T]/(g), so every remainder coefficient
is zero. Thus the identity specializes to every commutative A-algebra.

If one starts only with finite division-free arithmetic programs, extracting
their bidegree (1,1) part gives a bilinear algorithm with at most a constant
factor increase in multiplicative complexity. The factor is absorbed by
choosing the fixed base size sufficiently large before recursion. Lemma 6.1
of the rectangular source already supplies exact bilinear decompositions, so
that detour is unnecessary for its bounds.

### Uniformity versus existential base constants

The finite identity might have enormous size and coefficient heights. That is
compatible with the claimed asymptotic upper bound: it is fixed before the
input. Its algebraic coefficients have finite exact descriptions, so there is
one ordinary finite algorithm. One may also search finite algebraic tensor
identities and verify their equations exactly; the existence result ensures
that a search at suitable fixed parameters terminates. This establishes
existence, not a practically instantiated implementation or useful crossover.

## 3. Reduction modulo odd primes needs no field-extension theorem

For every odd prime q not dividing D, define

    A_q = F_q[T]/(g mod q).

The coefficients of the base algorithms have well-defined reductions in A_q,
and the polynomial tensor identities remain true. In particular, the same
division-free matrix algorithm works for matrices with scalar entries in the
embedded F_q inside A_q.

Three points remove potential hidden assumptions:

1. It is unnecessary for g mod q to be irreducible. A_q may be a product or a
   ring with nilpotents. The algorithm only uses addition and multiplication
   and fixed reduced constants, not inverses of arbitrary A_q elements.
2. It is unnecessary to exclude discriminant primes. Only denominators of
   the fixed coefficients require exclusion. Additional finite exclusions
   would be harmless but are not logically needed.
3. Since g is monic, the classes 1,T,...,T^(d-1) are an F_q-basis. Therefore
   F_q embeds injectively as constants. The algorithm's output on scalar
   inputs has the scalar matrix-product residue as its constant coordinate
   and zero in every other coordinate.

Arithmetic in A_q costs a fixed polynomial in d, hence a constant number of
F_q operations independent of the input size. Fixed coefficient reductions
and inversions of D modulo q cost polynomial time in log q. This is a direct
proof of the finite-specialization bridge; an all-characteristic MM theorem
is not required.

## 4. Exact transfer to the two-adic mode ring

Assume R_p is free of rank r(s)=poly(s) as a Z/2^p Z-module, p=poly(s), with
a specified integer multiplication table of polynomial bit length. This
includes

    R_p = (Z/2^p Z)[U,V]/(f(U),V^ell)

from the contraction interface, with its monic f and polynomially bounded
degrees. The number-field polynomial g above is unrelated to this f.

Write inputs A,B in the fixed module basis. For every ordered pair of module
coordinates i,j, lift their scalar entries to the integers in [0,2^p), and
compute the ordinary integer matrix product C_ij=A_i B_j. If the inner matrix
dimension is d_2, every entry is nonnegative and strictly below

    d_2 2^(2p).

Set B_0=2p+ceil(log_2 d_2)+1. It is polynomial in s under the interface's
assumption that logarithmic matrix dimensions are polynomial in s.
Use the first B_0 odd primes not dividing D. Their product exceeds 2^B_0,
hence exceeds the reconstruction bound. The number and numerical magnitudes
of these primes are polynomial in B_0, with constants depending on D. A sieve
finds them in polynomial time.

For each such prime, run the fixed bilinear algorithm over A_q, retain the
constant output coordinates, and reconstruct C_ij by CRT. Combine the C_ij
using the integer structure constants of R_p, and finally reduce modulo 2^p.
Process coordinate pairs and primes sequentially.

This uses polynomially many ordinary matrix multiplications and polynomial
bit work per arithmetic or table-entry operation. It gives the same leading
matrix-dimension exponent with a polynomial factor in s and the input
description length.

There is no ring homomorphism Z/2^p Z -> F_q for odd q; the algorithm does not
pretend otherwise. It lifts module coordinates and reconstructs integer
products before reducing modulo 2^p. In particular it never inverts 2, a
nilpotent, or a general nonunit in R_p.

## 5. A safe algorithm uniform in all encountered rectangular shapes

Let x >= y >= z >= 0 be the base-two logarithms of the three matrix
dimensions. Fix rational alpha_0 in (0,1), omega_0=9/4, and eta>0.
Choose once and for all:

- a finite base algorithm for outer dimensions N,N and inner dimension
  N^alpha_0, with exponent at most 2+eta;
- a finite square base algorithm with exponent at most omega_0+eta.

The slack may first be divided by a fixed factor to absorb bilinearization
and recursion factors. Since alpha_0 is rational, N can be chosen as a fixed
perfect power so all three base dimensions are exact integer powers.

If z >= alpha_0 y, set

    t_0=(y-z)/(1-alpha_0),
    t_1=(z-alpha_0 y)/(1-alpha_0).

Tensor products of the rectangular and square algorithms at these logarithmic
scales have dimensions (2^y,2^z,2^y). Round the two recursion depths upward;
because both bases are fixed, this changes dimensions and cost only by fixed
factors, uniformly even when one depth is zero. Their exponent is at most
(2+eta)t_0+(omega_0+eta)t_1.

If z <= alpha_0 y, pad only the smaller dimension and use the rectangular
algorithm at scale y. Blocking the largest dimension contributes x-y to the
time exponent. Consequently a uniform valid exponent is

    F(x,y,z)=max{x+y, x+v y+w z}+eta y,

where

    v = (1-alpha_0(omega_0-1))/(1-alpha_0),
    w = (omega_0-2)/(1-alpha_0).

A useful bound in the same two-linear-form format as existing certificates is

    F(x,y,z) <= max{(1+eta/2)(x+y), x+(v+eta)y+wz}.

The coefficients are:

| Source choice | alpha_0 | v | w |
| --- | --- | --- | --- |
| Narrow formal scope in 107.md | 23/50 | 85/108 | 25/54 |
| New rectangular theorem | 1/2 | 3/4 | 1/2 |

The first branch must retain its slack. Neither omega<=9/4 nor an exact
dual-exponent value asserts a finite algorithm whose cost attains that
infimum with no exponent slack.

Permuting the three dimensions is legitimate by permuting the three linear
factors of a finite tensor identity and executing the resulting bilinear
algorithm. It does not require a claim that transposing an existing program
automatically preserves its memory schedule.

### Warning concerning the full nonlinear rectangular curve

Theorem 1.1 is stated for each fixed shape. Calling a different abstract
algorithm for the exact aspect ratio of each input, while suppressing its
shape-dependent constants, is not a uniform algorithm proof.

Safe options are:

1. Use the two fixed endpoint algorithms above. This is sufficient for the
   conservative new numerical certificates.
2. Use a fixed finite set of rational shape anchors, triangulate their
   logarithmic shape cone, and tensor-interpolate within each simplex. The
   resulting piecewise linear upper bound is uniform. Rounding the finitely
   many recursion depths changes dimensions by fixed factors.

A naive finite grid that rounds every input aspect ratio upward produces an
additional exponential padding factor, including in space. It may be valid
with explicitly charged slack, but it does not justify an unchanged exact
input/output space exponent. Tensor interpolation avoids that problem.

### Fully uniform use of the nonlinear curve, with explicitly charged slack

For every fixed epsilon>0 there is one algorithm, uniform in all positive
integer matrix dimensions, whose time is

    poly(s+L) * 2^{G(x,y,z)+epsilon(x+y+z)}

and whose workspace remains poly(s+L)*2^(x+y). This is a consequence of a
finite rational triangulation, not an uncharged selection among infinitely
many shape-specific algorithms.

First pad dimensions to powers of two; this changes x,y,z by at most one.
Put S=x+y+z and h=(x,y,z)/S (the case S=0 is constant size). The sorted h
belong to a compact rational simplex. Choose a fixed rational triangulation
of that simplex of sufficiently small diameter. For each vertex h_j choose
one finite bilinear algorithm at that rational shape with slack epsilon/2.
The base sizes can all be powers of two: choose the parameter as a power of
two divisible in exponent by the denominators of h_j, then take the fixed
tensor power supplied by the asymptotic-rank definition.

If h=sum_j lambda_j h_j in its triangle, at most three lambda_j are nonzero,
and they are nonnegative with sum one. Tensor the corresponding algorithms
at logarithmic scales lambda_j S. Rounding each of at most three recursion
depths upward enlarges the dimensions only by fixed factors. Thus the input
shape is attained without an epsilon*S enlargement of the matrix arrays.
All triangle selection and depth rounding are rational computations on the
integer logarithmic dimensions.

The function G is continuous on this simplex, including the two branches'
common boundary and b=c=0. In fact it is 1-Lipschitz in the l1 norm on the
nonnegative cone. On the second branch put r=b/a and t=c/b. Then
0<r<=1 and 1/(1+r)<t<=1, and its partial derivatives are

    G_a = 1/2 + (1/t + (1-r^2)t)/4,
    G_b = 1/2 + (1/(rt) + (r-1/r)t)/4,
    G_c = 1/2 + (-1/(rt^2) + 1/r + r)/4.

Every derivative lies in [0,1]: the first two expressions are decreasing
in t and equal one at t=1/(1+r), while the third increases from zero to
1/2+r/4. The first branch has derivatives (1,1,0); the formulas match at
the branch boundary. Symmetric extension handles changes in dimension
ordering. Therefore a triangulation of l1 diameter at most epsilon/2 gives

    sum_j lambda_j G(h_j) <= G(h)+epsilon/2.

The summed exponent, including base slack, is at most
S(G(h)+epsilon)=G(x,y,z)+epsilon S. The library is finite, so one K and D
from Sections 2--3 serve it all. Along a recursion path there are O(S)
levels; even if a vertex has a zero coordinate, each array fits within a
fixed factor of the original largest array, giving the permitted polynomial
workspace factor. This establishes the claimed fully uniform formulation.

For an entropy certificate, the extra epsilon(x+y+z) must be bounded and
added to the local coefficient. It is not justified to omit it while citing
only the infimum exponent curve. An arbitrarily small fixed epsilon is
available if the improvement has strict slack.

## 6. Workspace audit

A fixed bilinear algorithm can form one pair of linear combinations of child
blocks, recursively multiply them, accumulate their contribution into parent
output blocks, and discard the child data. The number of coefficients and
blocks at a base step is a fixed constant. Along a depth-first path the
largest input/output block sizes decrease geometrically (all endpoints used
above have positive fixed exponents). Thus the workspace is a constant times
the largest input/output array size, up to polynomial factors for entry
representations and depth.

For mixed-base tensor products, perform the finite bases in any fixed order;
the same geometric bound applies. The rank lower bounds on each base tensor
ensure that linear-substitution work over all layers is bounded by a
polynomial in recursion depth times the number of scalar products.

The largest array has 2^(x+y) entries. For z<=alpha_0 y, padding the smallest
dimension never increases this largest pairwise product. CRT reconstruction,
number-field coordinates of constant degree, ring coordinates of polynomial
rank, and sequential processing of coordinate pairs add only polynomial bits
per cell. Hence

    workspace <= poly(s+L) * 2^(x+y),

including input and output arrays, while the time exponent is the F above.

For bit-machine implementations, layouts and reblocking must also be
charged. They can be carried out by sequential copying and sorting of
records in a polynomial factor per cell and per recursion layer, so no
unit-cost random access to exponentially large addresses is necessary for
the leading exponent. This is an implementation argument separate from
the source's arithmetic-complexity theorem.

## 7. Reporting recommendations

- Cite the current field result and the new descent/CRT lemma separately.
- State a fixed eta and retain it in every reported numerical coefficient.
- Present the .46 certificate as the conservative bound supported by the
  documented formal scope, and the .5 certificate as additionally importing
  the newer rectangular paper.
- Explain that new exponent coefficients are certified upper-bound
  improvements, not a change to the n log log n/sqrt(log n) exponent order.
- Do not call the finite verification code an implementation or benchmark of
  the imported fast multiplication algorithm.
- Do not claim local Lean compilation or machine verification of this new
  bridge and its composition with the SAT recursion.
