# An even frame and an odd anchor quotient

This is a new ordinary proof, formalizable in ZFC, for a modification of
package 131's signed direct C222 compiler. It introduces no logical axiom.
Its final centered polynomial has 319 unrestricted integer variables,
207 quadratic residuals, degree four, 5,779 collected monomials and
coefficient height 128,446. It is the sum of the squares of all residuals in
`generated/centered/equation.json`; every collected coefficient is in the
adjacent `expanded_polynomial.json`.

The inherited 324-variable baseline has 208 quadratic residuals, 5,808
collected monomials, and the same degree and height. Thus this particular
new endpoint improves variables, rows, and monomials simultaneously.
This is no global minimality or literature-priority claim.

## The exact change

All original affine atoms, front arithmetic, cap inequalities, and pooled
ordinate congruences remain as in package 131. Write the original square
frame as W=2+sum a_i^2. Replace it by

    W = 2 + 2 sum a_i^2.                                      (E1)

The retained frame equation is

    A^2 - W^3(W+2)(2z+1)^2 = 1.                               (E2)

Replace the ternary guard A>=0 by one fresh unrestricted integer a and

    A = 2a^2 - 1.                                             (E3)

In the anchor, C denotes the main Pell ordinate (named `cap.Y` in the
literal artifact). Replace

    J=C^2(e+1),  e>=0

by

    J=2C^2(2e+1),  e an unrestricted integer.                  (E4)

No guard is required on e. No other semantic guard is removed. The old
cap is C=W+1+sum y_i^2+u^2+v^2+w(w+1), so C>W>0. The comparison center is
still D=1+4J(2d+1), with its old congruences.

The manuscript notation C,D differs from the preserved source coordinate
names; the machine-readable transformation certificate records all names
and exact indices.

## Elementary Pell identities

For an integer b>=2 define X_n(b),Y_n(b) by

    (b+sqrt(b^2-1))^n = X_n(b)+Y_n(b)sqrt(b^2-1), n>=0.

The recurrence is X_(n+1)=b X_n+(b^2-1)Y_n and
Y_(n+1)=X_n+b Y_n. In particular

    X_(2n)=2X_n^2-1,  Y_(2n)=2X_nY_n.                         (P1)

If b is odd, X_n is odd for all n and Y_n is odd exactly when n is odd.
The latter assertion follows from Y_(n+1)=1+Y_n modulo two; the former
from the X recurrence. Repeated use of (P1) therefore gives

    v_2(Y_n(b))=v_2(n), n>=1, b odd.                          (P2)

For any i>=1 put c=Y_i(b). Expanding the c-th power of
X_i+c sqrt(b^2-1) shows c^2 divides Y_(ic): the first odd binomial term
is c^2 X_i^(c-1), and every remaining odd term contains c^3. Thus

    c^2 | Y_(ic).                                            (P3)

These are unbounded identities, not conclusions from a finite sample.

## Soundness

Equation (E1) makes W an even integer at least two and retains all old
strict frame bounds (in fact it strengthens them). By (E3), A>=-1. If
a=0 then A=-1, contradicting (E2), since W>0 and 2z+1 is nonzero.
Thus A>=1; (E2) again excludes A=1. Consequently A>=2, and (E3) also
makes A odd. This recovers the removed nonnegative guard before any
Pell classification, sign recovery, or growth estimate.

The old frame argument therefore applies unchanged. Its positive index
at center W+1 is a positive multiple of W, so A>=X_W(W+1)>W^W.
All small-residue inequalities used by the old pooled-index proof hold.

The cap gives C>W. Equation (E4) makes J nonzero and divisible by C^2;
its sign is immaterial. The common Pell norm gives

    |H|=X_l(A), |J|=Y_l(A)

for some l>=1. Since C^2 divides |J|, the inherited index-divisibility
lemma gives C|l and the same index comparison as before. Also
D=1+4J(2d+1) has |D|>=3 and D=1 modulo 4C. The comparison-norm proof
uses |D| and independent signs; it never needs J>0. It still identifies
the anchor index as W and hence C=Y_W(A).

All later source arguments are unchanged: the cap bounds every signed
principal index; the pooled squared-error residue identifies the signed
indices; q^t orients the first principal pair and recovers the factorial
front; the self-sized radix certifies all remaining powers; interval
products recover remainder signs; the factorial fixed point, prime-power
CRT, and Horn-flow argument give a finite C222 refutation. See the full
retained parent proof in `input/INHERITED_PROOF.md`.

## Completeness

Start from a finite C222 refutation and construct the same genuine front
values as the parent proof. Form the new W from (E1), so W is even.
Choose

    A=X_W(W+1), a=X_(W/2)(W+1).

Identity (P1) proves (E3). The recurrence
Y_(n+2)=2(W+1)Y_(n+1)-Y_n gives Y_n(W+1)=n modulo 2W. Therefore
Y_W(W+1)/W is a positive odd integer; setting

    z=(Y_W(W+1)/W-1)/2

proves (E2). This also explains why merely imposing A=2a^2-1 without
making W even would not justify the inherited odd frame parameter.

Choose every principal pair at its genuine index and put

    C=Y_W(A), U=X_W(A), l=2WC,
    J=Y_l(A), H=X_l(A).

By (P3), C^2 divides Y_(WC)(A), and by doubling 2C^2 divides J.
Since A is odd, (P2) gives v_2(C)=v_2(W), and therefore

    v_2(J)=v_2(2WC)=1+2v_2(C)=v_2(2C^2).

Thus J/(2C^2) is a positive odd integer. Set

    e=(J/(2C^2)-1)/2,

which is an integer satisfying (E4). The index l is even, so H is odd.
The Pell norm also gives gcd(H,J)=1, hence gcd(H,8J)=1. Ordinary CRT
therefore supplies a positive comparison center D with

    D=A modulo H,  D=1+4J modulo 8J.

The second congruence is exactly D=1+4J(2d+1) for an integer d. The
old comparison pair at index W and its signed quotient witnesses now
exist verbatim. The cap slack is nonnegative by the old Pell doubling
growth estimate (the enlarged W only strengthens it), and every remaining
guard and arithmetic row has the parent's canonical witnesses.

This constructs a new polynomial zero from every finite C222 refutation.
The new and old private witnesses need not agree pointwise; their
existence is what is proved equivalent.

## Logical calibration and proof boundary

The exact inherited logical interfaces are

    KEndpoint.c222_iff_zf_refutation
    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

The ordinary compiler and the argument above show, within ZFC,

    exists z in Z^319, P(z)=0  iff  there is a finite ZFC refutation.

Negating both sides yields the requested ZFC-provable equivalence
between no integer zero and Con(ZFC). No assumption of Con(ZFC),
omega-consistency, or reflection is needed for this equivalence.
This release does not provide a new complete Lean/Rocq or encoded
object-ZFC proof. Its executable certificates verify exact syntax,
projection, coordinate translations, and polynomial expansion; the
unbounded mathematical proof is the ordinary one given here and in
the retained calibrated dependency chain.

## Exact compilation

The source has unrestricted integer coordinates. Every remaining guard
G>=0 is represented by G=u^2+v^2+w(w+1). The elementary ternary theorem
represents every nonnegative integer in that form. Factoring is an exact
identity; monic integral elimination only removes a coordinate z=Q when
substitution keeps all residuals quadratic. Its certificate gives an
integral inverse. Final coordinate translations are integral bijections.
The two guard removals save six witness coordinates; (E3) introduces one
new coordinate. Thus 324 becomes 319, and one net residual disappears.
All coefficients remain explicit integers, with no exponentiation
operation or quantified coefficient port in the final polynomial.
