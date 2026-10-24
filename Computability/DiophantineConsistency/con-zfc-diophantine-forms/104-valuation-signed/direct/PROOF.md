# An integer quartic with 1,190 variables from synchronized direct certificates

This component supplies an explicitly materialized polynomial over the
unrestricted integers. It improves the signed-domain conversion of the
received synchronized direct-C222 construction, while preserving that
construction's arithmetic semantics and numerical-calculus calibration.
It uses neither K215 nor Jones's universal polynomial.

## 1. The exact polynomial and theorem

Let R_0,...,R_599 be the 600 quadratic residuals listed in
`output/equation.json`, in its stated order, on integer coordinates
x_0,...,x_1189. Define the one ordinary polynomial

    P_1190(x_0,...,x_1189) = sum_{j=0}^{599} R_j(x_0,...,x_1189)^2.

The complete expanded coefficient dictionary is
`output/expanded_polynomial.json`. A term `[c,[i_1,...,i_s]]` means
`c*x_(i_1)*...*x_(i_s)`; the empty list means the constant monomial.
All coefficients and coordinate indices in these files are literal integers.
No power with variable exponent, factorial, binomial, variable-length
product, unbounded search, or unspecified coefficient remains in P_1190.

The exact finite checks give 1,190 variables, degree 4, 26,411 nonzero
expanded monomials, coefficient height 83,900,628, and largest absolute
residual coefficient 4,556. Every variable is used. The statement established
by composing the proof below with the explicitly named parent calibration is

    ZFC proves: [there is no x in Z^1190 with P_1190(x)=0] iff Con(ZFC).

Here Con(ZFC) is the syntactic absence of a finite derivation of falsity in
the repository's sealed ZFC calculus. The parent identifies its numerical
C222 refutation predicate with that syntactic predicate. This is an ordinary
proof formalizable in ZFC; this contribution supplies no new complete Lean
proof term or derivation object in the encoded object-language calculus.
Neither consistency nor inconsistency is assumed, and neither is decided.

## 2. The frozen natural parent

`source/parent_natural.json` is an unchanged copy of the received synchronized
522-natural-variable equation. Its SHA-256 is

    8b983a7357d16201ac5b7dfa6e12e809692ee26a29383ae84e2af2b891994f48.

It has 400 quadratic residuals. Its single polynomial is the sum of their
squares, with 20,225 collected monomials and height 83,900,628. The complete
received package is retained under `upstream/synchronized/`, including its
construction, proofs, provenance, calibration copies, contraction
certificates, and independent verification program.

That parent directly encodes a finite C222 proof through a commutative Horn
flow, a finite accumulator path, CRT certificates, and synchronized Pell
graphs. Its global arithmetic proof simultaneously supplies one common
radix for the binomial graphs, one global power frame, and compatible
Pell-index witnesses. Those simultaneous-existence arguments are inherited;
we do not replace them by identifying independent existential witnesses.

The named logical calibration interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their source copies
and pins are in the inherited provenance. The latter uses the ordinary
constructible-universe proof of equiconsistency of ZF and ZFC. The complete
transitive Lean dependency closure is not claimed to have been rebuilt.

The new reduction starts only after this entire natural parent is fixed.
The first 522 coordinates and first 400 residuals of the integer checkpoint
are exactly unchanged JSON data to that parent. No arithmetic macro,
calculus rule, native constant, or shared-frame parameter is modified.

## 3. Domain inference from a residual

Suppose one residual is

    c*x + Q(y_1,...,y_s) = 0,

where c is a fixed nonzero integer, x does not occur in Q, and every
coefficient of -c*Q is nonnegative. Then the residual implies

    c^2*x = -c*Q.

For a monomial in Q, every variable occurring to an even power contributes
a nonnegative factor for every integer value. It therefore suffices to know
that the variables occurring to odd powers are nonnegative. Under these
hypotheses the right side is nonnegative, and c^2>0 gives x>=0.

This is a sign inference, not elimination by division. It introduces no
denominator or divisibility obligation. In the common monic case c=1 or
c=-1 it is simply x=P with P having nonnegative coefficients. The actual
certificate also uses one nonmonic instance: a source row equivalent to
16*A=20+4*T proves A>=0 from T>=0. This saves one further three-coordinate
guard, compared with using only monic inference rules.

The delivered certificate gives every target, source row, positive
multiplier c^2, scaled defining polynomial, and list of odd-power
dependencies. Its 288 inference steps are ordered. Each step uses only
nonnegativity facts already proved, so circular implications cannot be used
to manufacture an unconditional sign conclusion.

The remaining 234 coordinates are guarded explicitly. In fact they are
exactly the coordinates that are not the target of any eligible single-row
inference of the displayed kind. The closure from those 234 coordinates
reaches all 522. Thus this guard set is minimal for this particular inference
rule system; it is not asserted to be minimal among arbitrary arithmetic
arguments, normalization symmetries, or alternative presentations.

## 4. An exact quadratic nonnegativity guard

For every integer x,

    x>=0 iff there exist a,b,c in Z with x=a^2+b^2+c(c+1).

The reverse implication is immediate: squares are nonnegative and the
product of two consecutive integers is nonnegative.

For the forward implication, 4x+1 is 1 or 5 modulo 8 and is not divisible by
4. Legendre's three-square theorem represents it as a sum of three integer
squares. Modulo 4, exactly one of the three squares is odd. After reordering,
write the representation as

    4x+1 = (2a)^2 + (2b)^2 + (2c+1)^2.

Subtract 1 and divide by 4. This yields the required representation.

For each of the 234 selected source coordinates x_i append the quadratic
residual

    x_i - a_i^2 - b_i^2 - c_i^2 - c_i.

All guard variables are fresh and appear in only their own guard. The result
has 522+3*234=1,224 unrestricted integer coordinates and 400+234=634
quadratic residuals. Its exact expanded quartic has 23,590 monomials and
height 83,900,628.

At an integer zero all guards force their 234 coordinates to be natural.
Apply the finite ordered certificate from Section 3: the other 288 original
coordinates are natural as well. The retained source residuals therefore
give a natural zero of the parent. Conversely, any natural parent zero
extends to an integer checkpoint zero by the displayed three-square
representations, independently for each selected coordinate. This proves
existence equivalence in both directions. The extension is not unique.

## 5. Signed monic projection

Suppose a residual over Z is v-F(w)=0 or its negative, with F an integer
polynomial not containing v. Replace v by F in every other residual and
delete the defining row and coordinate. Projection is a bijection on the
integer zero sets; its inverse is v=F(w). No sign hypothesis on F is needed.
For a sequence of substitutions, apply these inverse maps in reverse order.

The received signed projection algorithm uses this elementary fact while
requiring every transformed residual to have degree at most two. Affine
restorations preserve that degree bound automatically. A quadratic
restoration is used only when the deleted coordinate occurs only as a
scalar multiple, never in a product with another coordinate, in every
other remaining row. The support cap controls expression growth and
never truncates a polynomial or affects the validity of a substitution.

Applied to the 1,224-coordinate integer checkpoint, the algorithm supplies
34 exact substitutions: 23 affine and 11 quadratic. No unconstrained
coordinate is discarded. Every guard constraint is preserved either as a
substituted residual or through the exact restoration formula of a deleted
guard row. In particular, a negative coefficient in a restoration does
not justify dropping a sign constraint; the reverse maps restore the whole
guarded checkpoint before Section 4's sign proof is applied.

The resulting equation has 1,224-34=1,190 coordinates and 634-34=600
quadratic residuals. Taking their sum of squares gives P_1190. Over Z a sum
of integer squares vanishes exactly when every residual vanishes. Combining
this with the two existence equivalences above and the parent theorem
proves the consistency equivalence in Section 1. Every argument is finite
algebra and ordinary arithmetic, valid over the internal naturals and
integers of ZFC, not merely over standard externally chosen witnesses.

## 6. Comparison and novelty boundary

| Construction | Integer variables | Degree | Residuals | Expanded terms | Height |
| --- | ---: | ---: | ---: | ---: | ---: |
| Received synchronized integer lift | 2,088 | 4 | 922 | 26,791 | 83,901,150 |
| Received batched integer endpoint | 1,690 | 4 | 842 | 21,381 | 2,649,643,805,758 |
| New inferred-guard checkpoint | 1,224 | 4 | 634 | 23,590 | 83,900,628 |
| New signed projection | 1,190 | 4 | 600 | 26,411 | 83,900,628 |

The new final equation reduces the preceding 1,690-variable direct endpoint
by 500 variables (29.59%) and 242 residuals (28.74%), while increasing its
expanded monomial count by 5,030 (23.53%). The coefficient height decreases
substantially. Against the synchronized 2,088-integer lift of the same
natural parent it improves every displayed measure except the unchanged
degree. The 1,224-variable checkpoint is retained as a smaller-expression
tradeoff. The 522-variable nonnegative equation is unchanged.

This is a new explicit combination and checked reduction of received
constructions. The three-square theorem, elementary positivity inference,
and monic elimination are standard facts. The result is not a claim of
worldwide priority, global minimality, a new fewest-variable record across
all degrees, or a new proof of incompleteness. In particular, existing
K215-based equations have far fewer variables; the contribution here is a
smaller complete direct-calculus quartic with ordinary small coefficients.

## 7. Independent finite validation

The independent `verify.py` imports neither the producer nor the optimizer.
It authenticates the frozen parent bytes; compares the complete source
prefix; checks every literal guard and every ordered sign inference;
replays all 34 integer substitutions and their coordinate maps; and
independently expands both complete polynomials. It rejects deliberate
changes to an inference coefficient, a guard sign, a restoration, and an
expanded coefficient without relying on a hash mismatch for those controls.
The separately supplied `verify_projection.py` is an additional projection
check using a different polynomial arithmetic implementation. Normal and
optimized Python executions preserve all checks because no correctness
test is written using `assert`.

The producer also rebuilds every new file byte for byte. The inherited
synchronized release has its own complete replay in the preserved upstream
directory. These finite checks establish the literal artifact identities;
they are not substitutes for the parent calculus calibration or the
unbounded Pell/CRT theorems. Their exact scope is recorded in the receipts.

## 8. Further research questions

1. Can a small collection of multi-row positivity implications reduce the
   234 forced seeds of the current single-row rule system?
2. Which Pell-coordinate sign changes remain exact symmetries after natural
   contraction, so that some signs can be normalized instead of guarded?
3. Can a simultaneous frame be designed directly over signed quotients,
   allowing earlier elimination before costly natural-domain contraction?
4. Can the 1,224-coordinate checkpoint be projected with a substantially
   smaller monomial increase? The delivered 1,190-point uses support cap 16;
   increasing it to 64 saved only one more coordinate while adding 5,938
   terms, so that alternative was not adopted.
5. Can the complete ordinary compiler proof be internalized in the encoded
   ZFC calculus while retaining this exact, already fixed coefficient list?
