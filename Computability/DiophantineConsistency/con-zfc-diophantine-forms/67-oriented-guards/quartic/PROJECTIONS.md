# Exact monic projections: 36-integer sextic and 32-integer octic

These are different degree/variable tradeoffs of the proved Q42, not
claims that the quartic itself has fewer than42 variables. No new number-
theoretic theorem or positivity convention is introduced.

## Integer projection lemma

Suppose a polynomial system over Z includes x-P(y)=0, where P has integer
coefficients and does not involve x. Delete this equation and substitute
P(y) for x in every other residual. Projection and the explicit reconstruction
x=P(y) give inverse bijections between its integer solutions and the new
integer solutions. There is no division, denominator branch, or saturation
condition. The same holds with an overall minus sign on that residual.

For several such definitions, substitute in dependency order. An acyclic
dependency graph ensures every reconstructed coordinate is an integer
polynomial in retained variables. Sum of squares of the remaining residuals
vanishes exactly when each does. Thus existential solvability, and therefore
the Q42 consistency equivalence, is preserved in both directions.

## Sextic in36 unrestricted integer unknowns

Starting from the literal Q42, remove these six coordinates and defining
residuals:

    w=4u²,
    C2=c²,
    F2=f²,
    Baux=I²,
    L=(beta J+1)²−1,
    E=a−(2v_scale+1)N.

The other21 residuals have degree at most3. The emitted sextic36.json
provides every substituted residual and reconstruction formula, with the
same whole coefficient binding. Its sum of squares has degree exactly6:
the coefficient of I^4 g^2 is1 even after the fixed coefficients are
specialized. The exact sparse expansion has435 symbolic terms.

## Octic in32 unrestricted integer unknowns

Instead remove these ten coordinates:

    w=4u²,
    X=(beta J+1)w,
    C2=c²,
    Delta=a²+4a+3,
    F2=f²,
    Baux=I²,
    g=y²−V²,
    L=(beta J+1)²−1,
    N=(beta J+1)(L+1),
    P=E(c−eta)+eta+zeta.

The acyclic substitutions turn the remaining17 residuals into polynomials
of degree at most4. Their sum of squares has exact degree8: its coefficient
of I^4 V^4 is1 on the actual fixed slice. The exact sparse expansion has395
symbolic terms. X is reconstructed after w, and N after L; neither is a
new quantified variable. The canonical output uses the fully substituted
expressions, not unresolved references to eliminated coordinates.

## Evidence and interpretation

build_projections.py verifies each removed row equals plus or minus its
monic defining polynomial, rejects dependency cycles, reconstructs every
expression, checks all eliminated symbols are absent, computes all residual
degrees and expanded sums, and certifies the two unit leading coefficients.
It uses SymPy1.14.0. Independent review checks the projection algebra again.
The generic integer projection lemma supplies the unbounded semantic proof;
finite sample assignments are not used in its place.

These new32/36 integer points must not be confused with the31-positive
source dimension or with a reduction in the unknown count of the9-positive
or10-integer high-degree forms. All three projected families preserve the
same explicitly inherited Q42/native compiler calibration. No global
minimum or new formal-kernel certificate is asserted.
