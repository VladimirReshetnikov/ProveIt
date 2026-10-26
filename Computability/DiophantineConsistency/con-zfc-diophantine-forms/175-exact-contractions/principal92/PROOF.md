# Proof of the literal 92-variable equation

## 1. The fixed finite definition

Let R_0,...,R_127 be the complete integer polynomials in
`sources/source191.json`, with source coordinates y_0,...,y_190.
The ordered free-coordinate list F, the retained-row list J, and the 99
triples (r,v,epsilon) are fixed literal data in `projection92.json`.
For each triple the raw source polynomial has the exact identity

    R_r(y) = epsilon*y_v + q_v(y),    epsilon in {-1,+1},

where q_v does not contain y_v. Set f_v=-epsilon*q_v. Give each free
coordinate its own independent integer input, in the order F. Define every
other y_v by y_v=f_v(y), following the acyclic dependency graph. Denote the
resulting 191-tuple of ordinary integer polynomials by sigma(x).

The promised single equation is

    P92(x_0,...,x_91) = sum_{r in J} R_r(sigma(x))^2 = 0.

There are exactly 92 free inputs and 29 retained rows. All 99 defining
polynomials are finite ordinary integer polynomials. The graph contains no
cycle, so this definition is finite and unambiguous. The literal binary
arithmetic circuit in `circuit92.json` is independently checked to be the
same polynomial. No interpretation of a mathematical predicate is needed
to evaluate it.

## 2. Integral elimination theorem

Suppose a finite system over Z contains epsilon*v+f=0, with epsilon a unit
and v absent from f. For every assignment of the other coordinates, the
unique possible value of v is -epsilon*f, which is an integer polynomial
in those coordinates. Replacing v by this value in every other residual,
and deleting the defining residual, therefore gives an integer zero-set
bijection. Its forward map forgets v, and its reverse map restores the
displayed polynomial.

The acyclicity condition in the literal certificate is checked at each
step after interpreting all earlier eliminated coordinates as polynomial
abbreviations. In particular, the checker rules out a hidden occurrence
of the new pivot through an earlier definition. This is stronger than merely
checking that the pivot symbol is absent from the raw printed right side.

Inducting through all 99 certified steps proves that sigma is defined over
Z, every deleted source residual vanishes identically after sigma, and the
remaining residuals are exactly the ones in P92. Thus

    sum_{r=0}^{127} R_r(sigma(x))^2 = P92(x)

as an identity of integer polynomials. Coordinate projection pi satisfies
pi(sigma(x))=x for every integer x. On the source zero set, the unique
defining equations imply sigma(pi(y))=y. This proves both soundness and
completeness, with no inequalities, sign hypotheses, or divisibility assumptions.

The same proof checks the preceding 29 unit projections from the explicit
220-variable source to the 191-variable source. The portable verifier
replays every sparse substitution and compares all 128 emitted source rows
coefficient by coefficient, including their coordinate renumbering. Composing
the two stages gives an integer zero-set bijection directly from the pinned
220-variable equation to P92, and the exact polynomial pullback identity

    P220(restore220(x)) = P92(x).

## 3. Exact degree 692

Assign degree one to each free coordinate and degree zero to an integer
literal. Bound the degree of each defined coordinate by the maximum, over
its source monomials, of the sum of the bounds of its factors. Apply the
same rule to every retained residual. This computes a rigorous upper bound
without expanding the substituted polynomial. The maximum retained residual
bound is 346, so the sum of squares has degree at most 692.

To show the bound is attained, use the explicit 92-integer vector a in
`verification.json` and specialize the free coordinates to x_i=a_i*t.
The coefficient of t^346 in retained source row R_61(sigma(a*t)) is
613639 modulo 1000003. It is therefore a nonzero integer. The verifier
computes that residue by homogeneous propagation through the exact finite
definitions, independently of the producer.

At least one residual consequently has degree 346. Over the real numbers,
the highest homogeneous part of a sum of squares is the sum of the squares
of the highest homogeneous parts. At the chosen integer vector this sum is
positive, so it cannot vanish identically. Therefore deg(P92)=692 exactly.

Nonzero reduction modulo the stated integer is used only as an exact witness
that an integer coefficient is not zero. No probabilistic polynomial identity
test is used to accept an identity or a zero coefficient.

## 4. Every input actually occurs

Syntactic liveness would not by itself exclude cancellation. The verifier
therefore evaluates the gradient of the final sum-of-squares polynomial
modulo 1000003 at one explicitly recorded 92-integer point. It uses ordinary
automatic differentiation through the literal additions and multiplications.
Every one of the 92 resulting partial derivative residues is nonzero.

For each i, the integer polynomial partial P92/partial x_i is therefore
nonzero, and x_i actually occurs in P92. The point and all 92 residues are
recorded in `verification.json`; the checker reconstructs them directly.
The number 92 is not padded with unused quantified variables.

## 5. Coefficient-height bound and circuit measures

For a polynomial f, let ||f||_1 be the sum of the absolute values of its
coefficients. The elementary estimates

    ||f+g||_1 <= ||f||_1+||g||_1,
    ||fg||_1 <= ||f||_1*||g||_1

allow a finite positive-integer bound to be propagated through the acyclic
source definitions. Set U(x_i)=1 for a free input and, for a source expression
sum c_m*product y_v, set

    U(expression) = sum |c_m|*product U(y_v).

The bound on the sum of the 29 residual squares is sum U(R_r)^2. This
integer has bit length 1655, so every expanded coefficient has absolute value
strictly less than 2^1655. The largest individual retained-residual bound
has bit length 828. Cancellations can improve the bound but cannot invalidate it.

The literal circuit has 2648 live nodes, of which 2428 are binary additions
or multiplications. The largest absolute integer appearing as a literal
is 46656. These are verified properties of the emitted circuit. They are
not the exact expanded coefficient height or the expanded monomial count,
neither of which was computed. Arithmetic gate count also does not measure
the bit complexity of evaluating very large input integers.

## 6. Composition with syntactic consistency

The parent 220-variable polynomial is the fully specified direct C222
construction in the pinned incoming *Integral Projection* archive. Its
identified ordinary arithmetic and logical calibration gives, in ZFC,
equivalence of an integer zero to a finite syntactic ZFC refutation.
The source uses the numerical calculus directly; this component does not
introduce a K215 execution or a Jones universal-polynomial parameter.

The finite algebraic bijections above preserve existence of integer zeros.
Composing them with that calibration and negating proves in ZFC

    (there is no x in Z^92 with P92(x)=0) <=> Con(ZFC).

No consistency assumption is used to choose the coefficients or prove the
equivalence. This is an ordinary mathematical proof formalizable in ZFC.
It does not assert that either side of the displayed equivalence is true,
and it is not a newly compiled end-to-end Lean/Rocq development or an
emitted object-language ZFC proof term. The containing submission retains
the named source and arithmetic proof boundary.

## 7. Comparison and attribution

The pinned report 152 explicitly supplies a direct-calculus equation in
94 unrestricted integers of exact degree 65540 with 28 residuals. P92
reduces the arity to 92 and the exact degree to 692, while retaining 29
residuals. Its degree is less than one ninety-fourth of that comparison
degree (65540/692 is about 94.71). The old 94-variable DAG's largest
literal is 256; the present literal is larger, 46656. Its reported
expanded-height upper bound is 2^164870, compared with the new certified
bound 2^1655. Bounds must not be confused with the actual expanded heights.

The general monic projection method was already used in reports 152 and
159. The new result is the explicit composition and measured endpoint,
with complete finite definitions and exact verification. No universal
simplicity minimum, worldwide priority, or proof of consistency is claimed.
