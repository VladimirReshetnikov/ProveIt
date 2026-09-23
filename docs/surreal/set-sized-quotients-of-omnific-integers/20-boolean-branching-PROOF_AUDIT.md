# Proof audit

## Research status

This is an internally checked, proof-bearing research draft, not independent
peer review or machine verification. The checks below describe the logical
obligations in the written argument. Finite computations do not discharge
its transfinite, class-theoretic, or arbitrary-support obligations.

## 1. Foundational convention

The article works in Godel–Bernays set theory with global choice. Each surreal,
individual support, coefficient tuple, and polynomial is a set. No infinite
degree polynomial, proper-class sum, or set of all class functions is used.
Class quotients may be coded using least-rank representatives. A set-indexed
family of class maps means a single uniform class relation with a set parameter.

The full surreal field admits bounds above and below every set of surreal
numbers. For a set of strictly positive exponents, a positive cut below that
set gives common monomial division of an arbitrary set of J-elements.
This is stronger than what is available inside every fixed Hahn field.

## 2. Radicality and monic certificates

The global ideal K = JN is radical. For x^m = sum a_j b_j in JN, choose a
positive monomial d such that a_j/d^m lies in J. Then (x/d)^m belongs to N.
Normality of N inside its ambient field implies x/d belongs to N, so x belongs
to JN. Properness is separately proved by a finite determinant argument and
constant coefficient; the proof never cancels in an unknown quotient ring.

For an integral ring extension D ⊂ C and an ideal I of D, an element x of C
belongs to sqrt(IC) precisely when it satisfies a monic polynomial whose
nonleading coefficients all lie in I. This follows from the determinant trick
in the finite subalgebra containing the finitely many witnesses. For x^q in IC,
substitute X^q into the polynomial certificate. Conversely the certificate
immediately puts a power of x into IC.

This certificate converts arbitrary ideal membership witnesses into a single
finite equation to which support projection can be applied.

## 3. Support projection

Projection onto exponents in a subgroup G is additive and F_G-linear, not
multiplicative on the full ambient Hahn field. In a coefficient of bx with
x supported in G, an exponent of b contributes to an exponent in G precisely
when that exponent of b is in G. Finiteness of Hahn convolution justifies the
coefficient comparison. No arbitrary exchange of an infinite family is needed.

Projecting a monic equation for x supported in G leaves the powers x^j unchanged.
It projects coefficients from A to A_G, and coefficients from J to J_G. This
proves exact descent for integrality and for radical ideal certificates.

Consequently, an element supported in G cannot acquire a new monic integrality
witness or become zero in the reduced fibre solely by using coefficients in a
larger support group. All local statements use radicals; the paper does not
assume J_G N_G is radical in general.

## 4. The dominant-scale algebra

Choose a positive exponent a exceeding every element of G, and put H=G⊕Za.
For k=F_G and T=omega^a, F_H is k((T^-1)). A nonnegative H-support has only
finitely many nonnegative T-degrees, since those integer degrees are bounded
above. Therefore A_H=A_G+Tk[T] and J_H=J_G+Tk[T].

At that scale take positive Laurent branches

    s0^2 = T^2 - 1,
    s1^2 = T^2/4 - 1,
    w = (1 - s0*s1)/2.

The exact identity

    w^2 - w = (T^4 - 5*T^2)/16

proves integrality and idempotence of the residue. It does not by itself prove
that the residue differs from 0 or 1.

The two radicands have independent square classes over k(T): their simple
zeros occur at disjoint pairs {±1} and {±2}. The branch extension has degree
four, and its polynomial algebra is free with basis 1,s0,s1,s0*s1. Consequently
there are well-defined specializations fixing k and sending

    T -> 0, s0 -> i, s1 -> i   (w -> 1),
    T -> 0, s0 -> i, s1 -> -i  (w -> 0).

These maps exist on the finite branch algebra, NOT on the Laurent field. The
proof never substitutes T=0 into a Laurent series.

## 5. Uniform splitting, including arbitrary larger-scale witnesses

If x is integral and supported in G and xw lies in global K, replace that
membership by a monic J-coefficient certificate. Project onto H. Its coefficients
now lie in J_G+Tk[T], and the entire identity belongs to the branch algebra.
Specializing w to 1 gives a monic J_G-certificate for x; therefore x was already
in K. The opposite specialization proves the same statement for x(1-w).

This handles all possible larger-scale ideal witnesses, not merely those visibly
present in the displayed formula for w. For a set-sized subring R of B_R, choose
one representative for each element and let G contain their supports. The same
w therefore splits every nonzero element of R simultaneously.

The multibranch version uses radicands T^2/r^2-1 for distinct positive r not
1. Every finite subfamily has independent square classes by its disjoint simple
zeros. The specialization proof is unchanged and realizes all finite patterns.

## 6. Boolean consequences

Set-length recursion supplies successive splitters over the ring generated by
all earlier ones. Every finite Boolean word times any nonzero original coefficient
survives. Finite Boolean atoms then prove injectivity of the free idempotent-variable
algebra. Infinite variable sets still mean finite polynomials, not full products.

For the explicit ordinal family, omega^alpha in the exponent field dominates
all finite rational combinations of omega^beta for beta<alpha. The support of
each earlier representative is in Z*omega^beta. Thus the same dominance proof
applies at every stage without constructing a class-valued history.

Atomlessness follows by splitting Z[f] for each nonzero idempotent f. If all
idempotents formed a set, the ring they generated would have a splitter belonging
to itself, contradicting e(1-e)=0. Splitting a proposed set of order-dense
idempotents similarly produces a nonzero part containing none of them.

## 7. Representation consequences and their extra inputs

These results additionally use the credited, reproved Boolean-power theorem
and small-image theorem. The coefficient copy of all algebraic integers is
not canonical. The integral doubling B_C ≅ B_R×B_R is established after
rationalization and descent through the exact characterization of integral
elements; it is not a CRT argument falsely assuming 2 is a unit in B_R.

A class ultrafilter selects one value on each finite Boolean partition. Global
choice supplies a set-like enumeration; at each ordinal stage the earlier
decisions form a set, so ordinary set-valued transfinite recursion with class
parameters applies. No proper-class use of Zorn's lemma is made.

For a set-indexed collection of small-target maps, their product target is a
set. Choose more independent idempotents than its cardinality. Two have equal
images, but their Boolean symmetric difference is nonzero, idempotent, and in
every kernel. This works in all target characteristics, including two.

To extend a branch agreeing on a prescribed set of elements, retain the set of
Boolean parts used in their finite decompositions, and freely adjoin kappa new
idempotents. Every binary assignment has the finite intersection property with
the old branch. Uniform class-ultrafilter extension gives 2^kappa distinct maps.

## 8. What the finite code actually verifies

`verification_results.json` records five groups: quadratic equations,
multiquadratic finite examples, initial Laurent coefficients, Boolean atom tables,
and finite support projection. All are exact rational or symbolic calculations.
The program does not establish the integral-closure theorems, class-size results,
or historical novelty. The written proofs, not the test count, carry those claims.

## 9. Explicit nonclaims

No full classification of the class Boolean algebra; no arbitrary infinite
joins; no saturation assertion; no global isomorphism B_R ≅ B_R×B_R; no
radicality claim for every fixed J_GN_G; no exact projective/global dimension;
no named classical factorization conjecture; no independent review; no Lean
verification; no successful repository build; no certified historical priority.
