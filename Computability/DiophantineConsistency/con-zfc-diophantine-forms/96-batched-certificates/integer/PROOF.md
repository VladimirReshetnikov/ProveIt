# A certified unrestricted-integer companion

The literal polynomial in `signed_output/expanded_polynomial.json` is denoted
by P_Z. It has 1,690 unrestricted integer variables, exact degree four,
21,381 nonzero monomials, and maximum absolute coefficient
2,649,643,805,758. Equivalently, it is the sum of the squares of the 842
quadratic residuals in `signed_output/equation.json`. Both files fix the
same coordinate order; there are no unspecified coefficient parameters.

This note proves, using the delivered finite certificates, that P_Z has an
integer zero if and only if the frozen 1,153-variable shared-frame equation
has a nonnegative integer zero. Composing this equivalence with the
shared-frame theorem and its inherited direct C222-calculus calibration
gives, within ZFC,

    (there is an integer zero of P_Z) <=> not Con(ZFC).

All consistency predicates and proof encodings here are the ones fixed by
the parent direct-calculus construction. No consistency assumption is used
in the equivalence. This note does not prove that P_Z has no zero.

## 1. A ternary nonnegative-value representation

For integers a,b,c define

    H(a,b,c) = a^2 + b^2 + c(c+1).

Its value is always nonnegative: two consecutive integers have a
nonnegative product. Conversely, let n be a nonnegative integer. The
positive integer 4n+1 is 1 modulo 4 and hence is not of the form
4^r(8s+7). Legendre's three-square theorem supplies integers u,v,w with
4n+1=u^2+v^2+w^2. Reducing modulo 4 shows that exactly one of u,v,w is
odd. After permuting them, write u=2c+1, v=2a, w=2b. Subtracting 1 and
dividing by 4 gives n=H(a,b,c). The argument includes n=0. Therefore

    n >= 0 <=> there exist integers a,b,c with n=H(a,b,c).

Legendre's classical theorem is the only additional unbounded mathematical
ingredient in this domain conversion. Its use and the elementary
consequences above are formalizable in ZFC.

## 2. Guard the original inputs before eliminating any coordinate

The frozen parent `source/parent_natural.json` has 1,153 variables and
1,021 quadratic residuals. Its variables consist of 795 arithmetic gate
outputs and 358 other coordinates (353 witnesses and five outer
coordinates). All coordinates have domain N, with 0 included.

Each of the 795 gate outputs g has an actual retained residual

    g - f(earlier coordinates) = 0,

where f has nonnegative integer coefficients. There are 710 multiplication
definitions and 85 addition definitions. The phrase "earlier coordinates"
means strictly smaller indices in the literal parent variable list. The
domain-conversion certificate identifies each of these 795 literal rows
and records its polynomial f. The independent checker verifies the exact
row identity, coefficient signs, complete gate coverage, and the strict
index ordering; it does not rely on a compiler's intended meaning.

For each of the original 358 nongate coordinates x, retain x and add three
private unrestricted integers a_x,b_x,c_x and the quadratic residual

    x - a_x^2 - b_x^2 - c_x^2 - c_x = 0.

Keep all original rows. The resulting system, listed in
`input/equation.json`, has

    1153 + 3*358 = 2227 integer variables,
    1021 + 358   = 1379 quadratic residuals.

Every natural solution of the parent extends to an integer solution of
this system by the ternary representation in Section 1. Conversely, any
integer solution gives nonnegative values to all 358 original nongates.
Induct in increasing order through the original variable list. A nongate
is nonnegative by its new guard. A gate is the value of its nonnegative
polynomial f on previously nonnegative coordinates, so it too is
nonnegative. The original 1,021 equations still hold. Thus restriction to
the original coordinates gives a natural solution of the frozen parent.

This order of construction is essential to the proof: positivity is
established on the full original triangular graph. Later elimination is an
exact equivalence of signed zero sets, so it need not preserve a visible
triangular positivity presentation.

## 3. Signed monic projection with exact reverse restoration

Suppose a system of integer polynomial equations contains a residual
v-f(y), or its negative, in which f is an integer polynomial independent
of v. Delete this residual and replace v by f(y) in every other residual.
Projection onto y is a bijection between the two integer zero sets; its
inverse is y |-> (f(y),y). In particular, no nonnegativity condition on
the coefficients of f is needed over Z. The deleted residual forces the
unique restoration, and substituting this value is exactly what is
required by every other old equation.

For a sequence of such operations, the restoration for a coordinate uses
only coordinates alive at that step. Reverse chronological restoration
therefore reconstructs every deleted coordinate as an integer. The
certificate checks this dependency condition at each step.

To preserve degree at most two in the residuals, this release allows
restorations f of degree at most two and checks every resulting row
exactly. Affine substitutions preserve quadratic degree. The optimizer
only proposes a quadratic substitution if v has no nonlinear occurrence
outside its defining row. The independent checker does not need to trust
that criterion: it performs the full substitution and tests the degree
of every resulting residual.

The delivered certificate performs 537 such eliminations: 308 affine and
229 quadratic. It deletes 446 original gate coordinates and 91 original
witness coordinates. No unconstrained coordinates are removed. Every
step deletes exactly one residual; no additional row becomes identically
zero in this schedule. Consequently the endpoint has

    2227 - 537 = 1690 integer coordinates,
    1379 - 537 = 842 quadratic residuals.

Negative coefficients in a restoration do not invalidate the original
sign guards. The checker substitutes into *all* remaining residuals,
including every affected guard. After reverse restoration the entire
2,227-variable guarded system holds, and Section 2 then proves
nonnegativity of every original parent coordinate. There is no circular
positivity argument and no instruction to discard a sign condition.

## 4. The single ordinary Diophantine equation

Write the 842 final literal residuals as r_1,...,r_842 and define

    P_Z(z_1,...,z_1690) = sum_{j=1}^{842} r_j(z_1,...,z_1690)^2.

For integer inputs, P_Z=0 if and only if every residual is zero. Every
residual has degree at most two, so P_Z has degree at most four. The
independently reconstructed coefficient dictionary contains degree-four
terms, proving that the degree is exactly four. The same reconstruction
checks all 21,381 nonzero terms, all coordinate indices, and coefficient
height 2,649,643,805,758. The maximum absolute residual coefficient is
1,122,540 and every displayed coordinate occurs in the equation.

Combining the preceding sections proves

    exists z in Z^1690: P_Z(z)=0
      <=> exists x in N^1153: P_shared_frame(x)=0.

The direct C222/Pell parent proof supplies the right-hand equivalence
with a ZFC contradiction proof. Every reduction used here is finitary
integer algebra or standard arithmetic formalizable in ZFC. Hence the
claimed equivalence of the *absence* of integer zeros with Con(ZFC)
follows inside ZFC from the parent's fixed proof-calculus calibration.

## 5. Literal identities, reproducibility and scope

The frozen natural parent's raw SHA-256 is

    a9e7293e6ae2dc82b43760af14b56fd00f23df769b8fc2c7405bcdcde990229c

`input/domain_conversion_certificate.json` binds the natural and signed
literal objects by canonical JSON hashes. It specifies all 795 gate
definitions and all 358 private sign guards.
`signed_output/terminal_elimination_certificate.json` binds the complete
input and output signed equations and gives all 537 reverse restoration
polynomials. The final equation's raw SHA-256 is

    ba7c214cda35183e567f61d208944ebce1f140de498d2df4744e58f8a166a4ed

The default `verify_integer.py` imports no builder or optimizer. It checks
the original pin, both literal conversion identities, every signed
projection step, and the complete final expansion. It rejects a removed
input guard and a deliberately corrupted restoration. With `--rebuild`
it additionally runs the builder in a temporary directory and compares
six primary artifact files byte for byte. Checks use explicit exceptions
and remain active under Python's `-O` option.

These finite computations certify transcription, domain conversion,
coordinate equivalence and exact metrics. The unbounded parent Pell and
proof-calculus theorems remain mathematical dependencies. The release
contains no new end-to-end formal kernel proof and makes no global
variable-minimality or priority claim. Its purpose is to supply a fully
explicit, independently replayable unrestricted-integer endpoint for the
new shared-certificate direct-calculus route.
