# Pell orientation and exact integer projection

## Precise contribution

The principal polynomial is the explicit sum of squares in
`equations/integer84_degree2097808.json`. It uses 84 unrestricted integer
unknowns, 23 residual polynomials, exact total degree 2,097,808, and 2,351 live
binary arithmetic operations in its supplied graph. The alternative graph with
suffix `literals256` defines the **same polynomial**, using 2,379 operations and
integer literal leaves of absolute value at most 256.

This construction composes credited ingredients: source 136's linear
orientation idea, source 173's reused CRT-index anchor, the incoming
`ConZFC_Cofinal_Pell_Compression_2026-10-25.zip` five-base power pool, and acyclic
unit substitution. The orientation principle is not new. The contribution is
its exact application to the newer source, the completely specified 84-variable
equation, and independently checkable finite reconstruction. No global minimum
or exhaustive priority claim is made.

## 1. The inherited arithmetic interface

The incoming source is the literal `principal206.json` in its `pooling/oriented_pool/`
directory. Its SHA-256 is
`7da179bedf0e072d01655aeb174516e94809294d67218b3db1c66a817f631e67`.
It has 206 unrestricted integer coordinates and 145 residuals: 144 quadratic
rows and one degree-12 five-base power-pooling row. This release retains that
source byte for byte as `parent206.json` and retains its complete original
archive as an explicitly identified dependency.

The source proves zero existence equivalent to a finite C222 refutation. Its
named logical calibration is `KEndpoint.c222_iff_zf_refutation`, followed by
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. These are inherited
ordinary mathematical dependencies; no fresh Lean or Rocq build is claimed.

Before orientation, the source's frame and independent anchor give

    W >= 258, |A-1| > 4W^3,
    0 <= j_i < W, |k_i| < W, i=1,...,14.

Each principal Pell pair has the form

    X_i = epsilon_i X_{j_i}(A),
    Y_i = delta_i Y_{j_i}(A),

with epsilon_i,delta_i in {+1,-1}, interpreted using the polynomial Pell
sequences at the possibly signed center A. Put rho_i=delta_i*j_i. Reduction
modulo A-1 gives X_i=epsilon_i and Y_i=rho_i. Negative A does not alter these
congruences because X_j(1)=1 and Y_j(1)=j as polynomial identities.

The source173 anchor uses the existing even CRT-index pair. The cap and anchor
classification do not use the old orientation row. The root selected below is
the separate index3 pair, and its coordinate is not used by the frame or anchor.
The remainder of the power-pooling and signed arithmetic bootstrap needs the
canonical pairs delivered by orientation, not its particular quotient formula.

## 2. Credited linear orientation, with its signed-center extension

Replace the old square orientation by

    sum_i [1-X_i + (Y_i-k_i)^2] = (A-1) Q,  Q in Z.       (1)

Modulo A-1, equation (1) makes A-1 divide

    E = sum_i [1-epsilon_i + (rho_i-k_i)^2].

Every term is nonnegative. Since there are fourteen pairs,

    0 <= E <= 28 + 56(W-1)^2 < 4W^3 < |A-1|.

Thus E=0. For every i, epsilon_i=1 and rho_i=k_i. All principal pairs are
therefore the required canonical signed-index pairs. The actual left side of
(1) need not be positive or small; it is the reduced representative E that has
these properties. Q must remain an unrestricted integer.

Conversely canonical pairs satisfy both congruences, so (1) has an integral Q.
The source quotient coordinate occurs in the old orientation row only; changing
it affects no other equation. The existing completeness construction therefore
supplies (1), and its soundness proof receives exactly the same canonical-pair
conclusion. This establishes equivalence of zero existence of the original and
modified systems, without assuming consistency or existence of a refutation.

Source136's manuscript contains this linear pool for a selected subset of pairs
at positive A. The all-pair signed-center instance above is the direct extension
needed here. It is not claimed as an independently new orientation mechanism.

## 3. Exact source binding

All coordinates here are the literal zero-based 206-coordinate chart. Set
A=x132+1 and Q=x193. The fourteen pair indices D,Y,Z are 136+3i,137+3i,138+3i,
for i=0,...,13. Set X_i=D_i+Z_i. The actual ordinate in pair i=2 is x143-1;
the actual product in pair i=10 is x168+1. All other Y,Z storage coordinates
are unshifted. The fourteen requested indices are, in order,

    x0, x2+x0, x8-1, x9, x10, x11, x12,
    x4, x13, x14, x1, x15, 2*x16, x93.

The actual products obey Z_i=A Y_i, and the fourteen norms are rows
95,97,...,121. The old orientation row135 is precisely

    sum_i [(X_i-1)^2+(Y_i-k_i)^2] - sum_i norm_i - (A-1)Q.

Replace row135 by the literal left side of (1) minus (A-1)Q. Every other
coefficient and every variable is unchanged. `orientation_certificate.json`
and both finite verifiers reconstruct these whole identities exactly. They do
not assume from variable names that a shifted wire is its unshifted value.

For explanatory purposes, the intermediate triangular row is old row135 plus
sum_i(X_i-1). On the AY rows, the difference between this triangular row and
the chosen affine row is

    sum_i(Z_i^2-Y_i^2) = (A-1)(A+1) sum_i Y_i^2.

Thus the two are related by the exact quotient shear
Q_tri=Q_aff+(A+1)sum_iY_i^2. This shear explains their equivalence; it does not
establish a novel pool beyond the credited source136 mechanism.

## 4. Why a coordinate disappears

The chosen affine orientation row has coefficient -1 at D_*=x142 and no
other occurrence of x142. Consequently it has the form

    -x142 + H(x0,...,x141,x143,...,x205)=0,

where H is an explicit quadratic polynomial. Deleting this row and substituting
x142=H in every other row gives a zero-set bijection over the integers. This is
the 205-variable source polynomial, of exact degree26. No divisibility, square
root, or sign condition is introduced by this projection.

More generally, let a selected source row have the form c*x_v+F=0, where c is
+1 or -1 and F does not involve x_v. Define x_v=-cF. If selected definitions
are acyclic and use distinct rows and variables, simultaneous recursive
substitution gives a polynomial restoration map. The deleted rows vanish
identically after restoration. The retained rows become exactly the delivered
residuals. Projection and restoration are inverse maps on the integer zero
sets. This elementary unit-substitution method is inherited, not novel here.

For the principal equation, 122 such rows are deleted from 145. The 84 remaining
coordinates are quantified independently over Z. The complete ordered definition
table and the retained-row list are in the JSON graph. Every earlier definition
is independent of x142 and x193, so adding the new unit definition creates no
cycle. The final polynomial is the sum of squares of the remaining 23 residuals.

As a matched control, the exact same 121 older definitions applied to the old
source give the supplied 85-variable control, with 24 residuals, the same exact
degree, and 2382 operations. The affine construction removes one coordinate and
one residual and saves 31 operations in the same blockwise evaluation convention.

## 5. Degree, input occurrence, and coefficient accounting

The graph's degree certificate first propagates a valid upper degree for every
unit-defined coordinate and each retained residual. It then evaluates the
highest possible homogeneous parts on an explicit integral direction modulo
the prime 1,000,000,007. A nonzero value at a maximal-degree residual proves that
its upper degree is attained. Since a sum of real polynomial squares cannot
cancel its highest homogeneous part, the final degree is exactly twice that
residual degree. This does not require expanding a degree 2,097,808 polynomial.

Separate reverse-mode derivative certificates show that every declared input
actually occurs. Coefficient-norm inequalities give a conservative bound
strictly below 2^8,582,228 for every expanded coefficient of the principal.
The exact expanded height and number of expanded monomials are not computed.
Integer literal leaves, coefficient height, and a height bound are different
measures. The bounded-literal companion pays 28 additional arithmetic gates to
construct the larger scalar coefficients from leaves of magnitude at most 256.

## 6. Final logical composition and limits

The ordinary argument gives, in ZFC,

    exists x in Z^84 with P84(x)=0
      iff the modified206 source has an integer zero
      iff the inherited206 source has an integer zero
      iff a finite C222 refutation exists
      iff a finite ZF refutation exists
      iff a finite ZFC refutation exists.

Negation is the requested equivalence between absence of integer zeros and
syntactic Con(ZFC). The argument does not prove either side unconditionally.
It concerns the internal natural numbers and finite proof codes of ZFC;
no external-standardness or transitive-model assumption is added.

The finite scripts authenticate the emitted polynomials, algebraic identities,
acyclic maps, degrees and actual inputs. They do not prove the unbounded Pell,
CRT, model-theoretic or logical-calibration theorems by testing examples. The
preserved parent archive identifies those dependencies and retains their
ordinary proof sources. No newly compiled end-to-end Lean/Rocq proof or encoded
object-ZFC derivation is claimed.
