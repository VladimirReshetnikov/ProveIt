# Independent review of sparse pair isolation

This review concerns the support-specific replacement of the global Sidon
certificate in ProveIt's packages 40 and 45. It is separate from the
inherited Jones and Sun number-theoretic reduction interfaces.

## Precise finite requirement

Let the source rows be integer polynomials of degree at most two in n
variables. Add a dummy variable x_0=1. Every source monomial x^alpha is
represented by a padded unordered pair of indices in {0,...,n}. A constant
uses (0,0), a linear monomial x_i uses (0,i), a square uses (i,i), and a
mixed quadratic uses (i,j).

Let w_0=0 and let all other weights be positive and distinct. The required
property is:

> For each padded pair appearing with a nonzero symbolic coefficient in
> any source row, its weight sum has exactly one representation among ALL
> unordered pairs, including pairs absent from every source row.

It is insufficient to check collisions only among supported pairs. But it
is unnecessary to forbid collisions between two unsupported pairs. The
delivered verifier checks the stronger, correct quantification above.

The fixed list used here has W=200. There are 71 active pairs among all
528 unordered pairs on 32 positions. Only 285 total sums are distinct;
130 positions have collisions and the largest collision multiplicity is
seven. Those counts are compatible with correctness because every active
sum is isolated from every other pair.

## Generic simultaneous extraction theorem

Write r_j(x)=sum_alpha a_(j,alpha) x^alpha and put

    e(alpha)=sum_i alpha_i w_i,
    c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) a_(j,alpha),
    H_j=2W+(j-1)(2W+1),
    D(Z)=sum_(j,alpha) c_(j,alpha) Z^(H_j-e(alpha)),
    C(Z)=(1+sum_i x_i Z^w_i)^2.

All exponents are nonnegative. Then, under the active-pair requirement,

    coefficient_(H_j)(C D)=2 r_j(x)

as an exact polynomial identity over the coefficient ring.

Proof: a term from row k can reach H_j only if

    H_j-H_k=e(beta)-e(alpha).

The right side is in [-2W,2W]. Distinct target exponents are separated by
at least 2W+1, so k=j. The pair alpha is active. Its sum therefore has no
other pair representation, forcing beta=alpha. The coefficient of x^alpha
in C is 2!/((2-|alpha|)! product alpha_i!), which exactly cancels the
factorial multiplier and leaves 2a_(j,alpha). Summing proves the identity.

## Coefficient and carry bounds survive inactive collisions

Within each row, distinct supported monomials have distinct exponent sums;
between rows, the kernel support intervals [H_j-2W,H_j] are disjoint.
Thus each D coefficient still corresponds to one source coefficient
recipe, and the predecessor's fixed bound M remains valid.

Coefficients of C are nonnegative on the natural witness domain, whether
or not its exponents collide. Their sum is exactly (1+sum_i x_i)^2.
Therefore every coefficient of C D has absolute value at most

    M(1+sum_i x_i)^2.

No global pair-sum condition enters this estimate. Consequently the same
digit padding, carry tests, source bounds, and ratio-bridge hypotheses
follow once the changed fixed exponents are substituted.

The final source row has positive constant coefficient one, so the top
coefficient of D is two. Positive nonzero weights ensure that no other
monomial can reach that same top exponent. The unconditional positivity
argument for D, which is needed before the carry theorem applies, survives
the support-specific replacement.

## Frozen dimensions and exact-degree interpretation

For n=31, m=22, and W=200, the targets are 400+401j for j=0,...,21.
The last target is 8821 and the product-degree enclosure is 9221. Starting
at 400 is valid: zero is an allowed source exponent, and no negative
exponent occurs. This saves one target slot compared with starting at401.

The positive nine-variable circuit has 652 live operations and the natural
version has 655, both of exact degree 32,568,568. The signed ten-variable
circuit has 653 live operations and degree 59,564,744. These values describe
the emitted arithmetic DAGs under the charged binary-operation convention.
They are not monomial counts of the fully expanded polynomial and do not
give a global minimum among all Diophantine representations.

For the nine-variable certificate, the source degree parameter is

    t=3(Hmax+3W+2)=141W+69.

The inherited cancellation-resolved finalizer identity then yields

    degree=1152t+12W+280=162444W+79768=32,568,568,

with nonzero diagonal leading coefficient 2^2050. The certificate's exact
ring identities justify replacing the primary circuit by its
cancellation-resolved version; random evaluations alone would not justify
this identity.

A nonzero diagonal leading coefficient computed in a prime field, together
with a valid total-degree upper bound, is a deterministic lower-bound
certificate for the integer polynomial at the actual fixed coefficients.
It should be distinguished from random evaluation agreement, which is
diagnostic evidence for an identity rather than its proof.

## Boundary of the review

The isolation theorem is a new sufficient condition for this concrete
coding replacement. The finite search produces a certificate of that
condition; optimality of W=200 is not proved. The source residuals, complete
coefficient tuple, Jones ratio interface, Sun ten-integer interface, and
machine/refutation calibration retain their stated provenance. This
review establishes no new end-to-end Lean/Rocq certificate and does not
decide the existence of a zero.
