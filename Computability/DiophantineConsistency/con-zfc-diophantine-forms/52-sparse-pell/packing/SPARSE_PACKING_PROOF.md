# Sparse active isolation and overlapping target bands

## Precise finite input

The source is the 31-positive-variable, 22-quadratic comparison circuit whose
SHA-256 is ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48.
It is copied as `data/source_system60.json`, interpreted as data, never executed.
After substituting n_i+1 for each positive variable, write its residuals as
q_j(n)=sum_alpha p_(j,alpha) n^alpha. There are 136 nonzero coefficient records,
but only 71 distinct active monomials: the constant, all 31 linear monomials,
and 39 quadratic monomials. The four coefficient ports are beta,K0,MC,MF.
Their fixed coherent payload binding is supplied separately in the archive.

Append a formal padding coordinate X_0=1. For |alpha|<=2 let
alpha_0=2-|alpha|, and put

  m(alpha)=alpha_0 c + sum_i alpha_i w_i,
  f(alpha)=alpha_0! product_i alpha_i!.

The main certificates use c=0 and positive w_i; the more general notation
also permits an interior padding position. Put

  C_z(T)=(T^c + sum_i z_i T^w_i)^2,
  D(T)=sum_(j,alpha in supp(q_j)) f(alpha) p_(j,alpha) T^(H_j-m(alpha)).

Every H_j is a fixed nonnegative integer, not a new unknown.

## The exact separation hypothesis

Let E be all 528 degree-at-most-two monomials in 31 variables. Require
H_j-m(alpha)>=0 for every active source term and, for every active (j,alpha),
every beta in E, and every target H_k,

  H_j-m(alpha)+m(beta)=H_k
    if and only if j=k and alpha=beta.                         (S)

This is the sole positional separation condition. It does not require all
528 monomials to have distinct weights. It also does not require disjoint
source bands or regular target spacing.

### Simultaneous extraction theorem

Under (S), for every tuple z in Z^31 and every row j,

  coefficient_(T^H_j) [C_z(T)D(T)] = 2 q_j(z).

Indeed, expand the square by its 528 formal multinomial terms, retaining
their labels even when irrelevant terms have equal exponent. A source term
(j,alpha) can reach a target H_k only with beta=alpha and k=j, by (S).
Its multinomial multiplier is 2!/f(alpha), canceling the f(alpha) in D.
This proves the identity coefficientwise over Z[beta,K0,MC,MF,z_1,...,z_31],
not merely at finitely many sample witness values.

### Collision and magnitude lemmas

Condition (S) itself implies that different active source records occupy
different exponents in D. For if
H_j-m(alpha)=H_k-m(beta), multiplication by the beta term would hit H_k,
so (S) forces j=k and alpha=beta. Consequently, if every weighted source
coefficient has absolute value at most M, then every coefficient of D has
absolute value at most M. No factor22 is introduced by overlapping bands.

For nonnegative z, every coefficient of C_z is nonnegative and their sum
is (1+sum_i z_i)^2. The coefficient at any exponent of C_z D therefore has
absolute value at most

  M (1+sum_i z_i)^2.

This remains true despite arbitrary irrelevant collisions in C_z: collect
them or retain their formal labels, and the same triangle bound results.
For 0<=z_i<b, this is at most M(31b)^2. These are precisely the bounds
needed by the existing binary no-carry source theorem.

If the largest exponent of D is d, its coefficient is2, and every other
coefficient is bounded by M, then D(B)>0 for every integer B>M+1. The
absolute sum of all lower contributions is less than
M B^d/(B-1)<B^d, whereas the leading contribution is2B^d.

## Two independently checked main certificates

The 31 weights, in the source's variable order, are

  9,89,38,43,2,118,82,27,88,83,23,163,123,148,3,108,
  144,155,137,173,174,68,17,107,63,57,169,168,28,133,102.

Their maximum is174. With padding0 the 528 formal quadratic monomials
occupy only265 exponent positions;117 positions have multiplicity greater
than1, with maximum multiplicity8. Thus this certificate is explicitly
NOT a B2/Sidon set. Nevertheless, every one of the71 active monomials is
isolated from all528. The263 repeated pair labels have been placed
entirely among irrelevant monomials.

Rows are ordered1,2,3,4,6,7,...,22,5, as in the preceding construction.
The regular certificate uses H_j=349j, for1<=j<=22. Then

  Dmax=7678, Kcode=Dmax+2W=8026.

Distinct rows are separated by more than2W, so active isolation alone
implies (S). Compared with the former W799,Hmax35178,Kcode36776, this
reduces both the digit-position maximum and the source degree scale by
more than three quarters, without changing any arithmetic bridge theorem.

The packed certificate instead uses, in that same row order,

  63,3297,4744,1100,752,3094,2209,3586,912,4689,2437,
  4168,3833,2764,78,4364,425,1347,1548,1614,1882,5074.

Thus Dmax=5074 and Kcode=5422. Source bands overlap substantially, but
all71808 source-record/expansion-monomial pairs satisfy (S). The largest
target belongs to original row5, whose shifted constant coefficient is1.
Therefore the largest coefficient of D is exactly2 in both certificates.
The packed variant lowers degree further; its irregular exponent arithmetic
may require more operations, so both variants are retained rather than
silently claiming one dominates in every metric.

## Substitution into the arithmetic source

For the main c=0 certificates, keep the established source formulas but
replace W,H_j,Dmax,Kcode and D by the certified values. In particular

  N0=B^(W+1), N1=4 B^(Kcode+1), N=N0 N1,
  Mask=N0-1-(b-1)sum_i B^w_i,
  T=Mask+(B-2)N0 sum_j B^H_j,
  J=2(1+g)^2D(B)+B sum_(e=0)^Kcode B^e.

The existing no-carry proof only uses the distinct positions of the target
mask and extraction identity, not equal spacing of the targets. The D
coefficient bound and leading positivity have just been proved with exactly
the same M. All integer bounds, coefficient buffers, and no-carry equivalences
therefore remain valid. The inherited nine-positive and ten-integer bridges
can use either certificate with their supplied refinements.

For an interior-padding certificate, the sole algebraic change
is replacing (1+g)^2 by (B^c+g)^2, and allowing one of the variable weights
to be0. The size bound B^c+g<=3bB^W still holds for0<=g<2bB^W, provided
0<=c,w_i<=W. The lower completeness bound b<=g holds when every source
zero has a positive coordinate at a positive weight. For this source no
zero can be supported on a single coordinate: row1 has support variables
J,L and nonzero constant1-beta^2-2beta for positive beta, whereas row5 has
support variables E,a,X and constant1. Their supports are disjoint. Thus
at most one zero-weight variable causes no difficulty. This condition is thus proved for the interior certificates below.

## Verified interior-padding certificates

A second independently checked active-isolation vector places the padding
coordinate at c=81 and the31 variable coordinates at

  51,169,164,28,174,146,0,32,20,24,154,45,143,140,33,141,
  44,123,135,11,119,148,145,18,166,1,158,25,163,29,5.

The zero-weight variable is i, which appears in neither row1 nor row5.
The general no-single-coordinate-zero argument above is therefore stronger
than needed here: row5 by itself forces a positive-weight coordinate to be
nonzero in any simultaneous zero. For the regular targets349j, this gives
Dmax7516 and Kcode7864; the largest target remains7678.

For the packed interior certificate, the targets in the same row order are

  4129,3084,1260,1688,1956,1467,2840,2579,3568,3318,4352,4608,483,793,3980,1039,2332,3719,3313,2101,162,4890.

Here Dmax4728, Kcode5076, and the largest target4890. The leading term is
again exactly2 and is the constant monomial from original row5. In particular,
Dmax must not be confused with the largest target when using interior padding.
All source bounds use Dmax, the product degree uses Kcode=Dmax+2W, and the
independently checked extraction ensures every target is at most Kcode.

The search originally returned32 positions with minimum1. Subtracting1 from
all32 positions, including padding, preserves every pair-sum equality and
inequality: each homogeneous quadratic monomial weight decreases by exactly2.
The certificate stores both vectors and this normalization; the independent
verifier checks it directly. All row signs remain+1, so no sign convention or
coefficient-positivity assumption has been hidden in the packing.

## Verification and search status

`verify_certificate.py` is newly authored and uses only the Python standard
library. It reconstructs all35-variable sparse polynomials from the pinned
60-gate source, applies the input shifts, checks every symbolic coefficient
against each certificate, verifies all factorial weights, and exhaustively
checks71808 term/expansion pairs. It also checks D coefficient uniqueness,
nonnegative exponents, target uniqueness, Dmax,Kcode, and leading coefficient2.
The resulting `VERIFICATION.json` is reproducible with

  python3 verify_certificate.py

The optimizer is not part of the proof. Its only output used by the theorem
is the short integer certificate independently replayed above. No claim of
optimality among sparse encodings, target packings, or Diophantine equations
is made. The Con(ZFC) equivalence additionally uses the identified inherited
compiler/K215 endpoint and the arithmetic bridge proofs; a finite positional
check alone is not an end-to-end formalization of those dependencies.

### Wider witness interval used by the nine-variable source

If the nine-variable bridge uses the wider interval0<=g<4bB^W, interior
padding still gives the same bound used at padding0:

  B^c+g < (4b+1)B^W <= 5bB^W, for b>=1 and0<=c<=W.

Thus any nine-variable coefficient budget based on(5bB^W)^2 remains
unchanged. This bound is separate from the sharper3b bound on the Sun
interval0<=g<2bB^W; one must use the bound matching the bridge's actual
witness interval.

### Uniformly shifted packed variant for faster homogeneous evaluation

`CERTIFICATE_174_interior_packed_shifted.json` adds186 to every packed
interior target and every exponent of D. Thus its new D is exactly T^186
multiplied by the preceding D, preserving all extraction identities and
coefficient bounds. It has minimum target348=2W, Dmax4914,Kcode5262,and
maximum target5076. The independent verifier checks the complete shifted
certificate, rather than relying only on this translation argument. A common
homogeneous degree-two evaluator can now be used without negative powers;
this trades a small degree increase for potential operation-count savings.
