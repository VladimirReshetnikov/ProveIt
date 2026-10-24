# Certified nonnegative quadratic contraction

## 1. The exact elimination theorem

Let a system of integer polynomials of total degree at most two have a row
`epsilon * (z - P(x)) = 0`, where epsilon is 1 or -1, z does not occur in P,
and P has integer coefficients. Suppose an exact certificate supplies

    P(x) = sum_j q_j L_j(x)^2 + R(x),

where every q_j is a positive rational, every L_j is an affine polynomial
with rational coefficients, and every coefficient of the integer polynomial
R is nonnegative. Then P takes nonnegative integer values on every tuple of
nonnegative integers. Integrality follows from P's integer coefficients;
nonnegativity follows from the displayed identity.

Delete the defining row and substitute P for z in every other row. Projection
and the restoration z=P are inverse maps between the two natural zero sets.
The implication in each direction is literal polynomial substitution, and
the inverse has the required natural domain by the certificate above.

An affine restoration preserves the degree-two bound everywhere. A quadratic
restoration preserves it if z occurs only as an isolated linear monomial in
all other rows. The producer enforces that sufficient restriction and the
independent checker also expands every resulting row and verifies degree at
most two. The final sum of squares therefore remains an ordinary quartic.

For a sequence of eliminations, restorations are applied in reverse order.
Any unused coordinate is freely chosen as zero; apart from such unused free
coordinates the maps are bijections. This argument is elementary algebra
and ordering of rational numbers and is formalizable in ZFC.

## 2. Producing certificates by exact rational linear algebra

The producer homogenizes a candidate quadratic using an extra formal
constant coordinate 1, giving a rational symmetric Gram matrix. Exact LDL
elimination with a positive diagonal pivot writes each positive-semidefinite
matrix as a positive rational weighted sum of squares. A negative diagonal,
or a nonzero matrix whose remaining diagonal entries are all zero, rejects
the candidate. There are no floating-point tolerances.

Three sufficient recognizers are attempted: the whole polynomial is PSD;
positive mixed/linear terms are moved to the nonnegative remainder; or only
positive edges connecting distinct negative-edge components are moved there.
These are intentionally incomplete recognizers. Failure to recognize a
polynomial makes no claim that it takes negative values.

The independent checker imports no producer code and need not trust LDL.
It multiplies every supplied affine square using Fraction arithmetic,
collects all terms, and demands exact equality to the original integer
restoration. It separately verifies that all weights are positive and all
remainder coefficients nonnegative. Every pivot, coefficient substitution,
degree bound, coordinate renaming, and expanded quartic is then replayed.

## 3. The source gate identity

The previous two-rail compiler represents a signed polynomial by positive
and negative rails (P,N), with semantics P-N. Its pair operations implement

    (P-N)+(Q-R), (P-N)(Q-R), (P-N)^2.

The new local checker is already a sum and product of squares and sums of
squares. It can compute these nonnegative quantities directly with the
quadratic gate z=(a-b)^2. There is no need to expand each square into two
nonnegative rails before compiling it.

For the guarded bundle the useful additional ring identity is

    c^2+ab-c(a+b) = (c-a)(c-b).

Consequently its square is `(c-a)^2*(c-b)^2`, using only nonnegative
intermediates. The complete local polynomial is unchanged, not merely its
zero set. The old monotone two-rail evaluation may still be used as a majorant;
alternatively replacing every difference square by the square of the sum
gives a certified monotone upper circuit.

`source_identity.py` independently traces the old factored source function
and the new direct source function. It verifies ten literal code-constructor
DAGs agree, then gives those common outputs algebraically independent names
and checks the remaining ring identity in exact factored normal form. The
guard factorization is separately checked by coefficient multiplication.
This finite audit supports the transcription claim. The algebraic identities
above are its unbounded mathematical proof.

## 4. Projected eight-column source review

For each ordinary axiom code h, the source substitutes p=q=0 and v=h into
the inventory relation, obtaining `S'*(1+M*h)=S`. Truth gives S'=S.
The bundle branch adds its displayed arithmetic guard. Modus ponens uses
p=a, v=b, q=I(a,b), hence

    S'*(1+M*b)=S*(1+M*a)*(1+M*I(a,b)).

Generalization uses p=b, q=0, v=A(a,b). Thus each projected branch has exactly
the existential meaning of the corresponding original branch. Products
encode disjunction of zero residuals, and the outer sum of squares keeps the
two beta-sequence equations conjunctive. Every factor is nonnegative.

For completeness, pad a finite refutation with truth steps until its length
t bounds every schema and inference parameter used in the projected columns.
Truth has the identity inventory transition, so padding preserves endpoints.
The parameters come from the finite syntactic proof and do not depend on M.

If the exact constructor majorant gives every label plus one at most
`(t+1)^C`, set m*=(t+1)^C-1. Then all labels and parameters are at most m*, and
the chosen carrier `M=((t+1)^t)^C` is exactly `(m*+1)^t`, the old admissible
inventory carrier. No circular bound t>=M is required.

Replacing each square difference `(u-v)^2` by `(U+V)^2` in the upper circuit
is sound whenever 0<=u<=U and 0<=v<=V. Addition and multiplication preserve
these bounds. The final majorant includes the local value, t,x,y, and 1, so
its emitted power H is strictly greater than each local value and bound.

Finally, with T=H! and B=product_{j=1}^t(1+jT), the canonical index defined by
`1+(Cindex+1)*T=B` is an integer >=0 and satisfies Cindex=i modulo
`1+(i+1)T`. Indeed T is invertible modulo that modulus. This retains every
local index without an existential CRT-index quotient.

The review establishes the new interfaces. It imports the named original
C222/calculus calibration and shared arithmetic certificate theorems; it
does not turn finite polynomial tests into a proof of consistency.
