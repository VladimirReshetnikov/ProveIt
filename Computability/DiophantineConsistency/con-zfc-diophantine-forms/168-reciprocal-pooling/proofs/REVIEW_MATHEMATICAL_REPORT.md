# Independent mathematical review of the final manuscript

Reviewed on 25 October 2026. This is a separately assigned AI mathematical
review, not external human peer review or a proof-assistant certificate.

## Verdict

**PASS for the new mathematical arguments, the printed first-section equation
definitions, the measured comparisons, and the stated proof boundaries.**
No unresolved substantive mathematical error was found in the reviewed
manuscript. The two theorem-statement clarifications requested during review
have been incorporated: W is explicitly an integer, and both base-square
bounds are imposed independently of whether their request blocks are empty.

The reviewed main manuscript is `report/report.tex`, with SHA-256
`c18fd98545ca7ae80d6b4c081f65358efd0b7d93ff09a3c3a4848568147a069b`.
Later purely typographical changes or generated appendices can change that
byte hash. This review is mathematical; the final PDF layout and generated
residual-appendix transcription require their separate checks.

## Read scope

The review read the complete main manuscript, the new projection proof,
the reciprocal-pooling proof and independent review, the package158
same-base-pooling and strict-horizon/bootstrap proofs, and the retained
named calibration-interface source files. It also examined the frozen
principal and companion coefficient data and their reciprocal certificate.

The complete transitive Lean/Rocq developments were not recompiled. The
parent arithmetic construction and its C222/ZF/ZFC calibration remain
identified inherited dependencies, as the manuscript repeatedly states.
This review does not relabel an inherited result as a freshly checked
end-to-end formal theorem.

## 1. The explicit companion formula matches the actual polynomial

A separate standard-library calculation, importing no producer module,
reconstructed the first-section formula directly from the final protected
218-variable quadratic residual list. It set x214,x215,x216,x217 to zero,
kept x0,...,x213 in their exact order, and used

    q = v95-1,                 A = v135+1,
    E0 = Qhat154+q*Qhat153,
    E1 = Qhat152+(q+1)*Qhat151,
    T0 = 2*A*q-q^2-1,
    T1 = 2*A*(q+1)-(q+1)^2-1,
    R = E0*T1+E1*T0-v214*T0*T1.

Every one of the retained151 residuals agrees with the companion JSON,
and R agrees coefficient by coefficient with its last residual. The
independently expanded sum of all152 squares agrees with all99,914
coefficients in the companion's saved expansion. Thus the concise
first-section formula is an exact finite specification of the supplied
polynomial, not merely a description of an equivalent polynomial.

The coordinate and row offsets in this formula are correct. In particular,
q is v95-1 rather than v95, A is v135+1 rather than v135, and the q block
uses rows153,154 while q+1 uses151,152. All four deleted coordinates are
absent from rows0 through150.

The coefficient of v214^2*v95^8 in the complete companion polynomial is
exactly1. The other151 squared residuals have degree at most4, so the
claimed exact degree10 follows. The arithmetic metrics recomputed in this
review are:

| Polynomial | Variables | Residuals | Degree | Collected terms | Polynomial height | Residual height |
|---|---:|---:|---:|---:|---:|---:|
| Principal |218|155|4|34,984|113,304|240|
| Companion |215|152|10|99,914|113,304|240|

The reported numerical differences are correct: seven principal variables
and residuals saved against225; coefficient height reduced by15,142;
27,117 additional principal monomials; then three more variables and
residuals saved by pooling at a further64,930 monomials.

## 2. The integral projection argument is valid

For the common-Hessian lemma, the identity

    R_i(y+s*d)=R_i(y)+s*a_i

follows from every Hessian annihilating d. The unit slope a_r=+1 or-1
gives the integral, uniquely determined value s=-a_r*R_r(y). The displayed
lift and projection are inverse on the respective zero sets, and no
nonunit division or unstated congruence condition is introduced. Since
the resulting residuals are constant linear combinations of quadratic
polynomials, degree at most2 is preserved.

The affine chart in the manuscript satisfies the stated hyperplane
identically. Direct substitution verifies its four integral inverse
formulas. It parametrizes every integer point of that hyperplane; the
implicit divisibility of the difference of two old coordinates is a
consequence of the hyperplane equation, not an additional assumption.
Retaining row19 while omitting row6 is correct because their exact
difference is the hyperplane equation. The final affine row has unit
coefficient on the deleted coordinate, so the last substitution is also
an integral zero-set bijection.

The protected residual-basis operations preserve simultaneous zeros
because each elementary row operation has an explicit integer inverse.
The manuscript correctly distinguishes equality of zero sets from
equality of sum-of-squares polynomials. The four protected pool rows and
their private coordinates remain the literal semantic interface for the
next step.

## 3. The reciprocal theorem and bootstrap are sound

The independent unbounded arithmetic proof is recorded in
`RECIPROCAL_POOLING_INDEPENDENT_REVIEW.md`. The manuscript faithfully
includes its crucial points:

1. The canonical Pell map is multiplicative modulo its own modulus and
   supports signed indices because the base is a modular unit.
2. The exact squared-error identity converts the polynomial equation
   into integrality of a rational sum.
3. Multiplication by C^2 clears negative indices, and replacing each
   numerator by a congruent numerator changes the rational sum by an
   integer. No pairwise coprimality of moduli and no inverse of C are used.
4. The bounds on the cleared errors and the moduli are strict and valid
   for the stated integer W and b. The errors built from the large Pell
   coordinates are not incorrectly treated as small.
5. The moduli have a common sign, so cancellation of nonzero squares is
   impossible once the rational sum is the integer0.
6. Negative indices at nonunit bases are ruled out by integrality; unit
   bases retain the correct signed-power meaning.
7. True powers restore each individual divisibility condition and hence
   the old integer K,L witnesses.

The early bootstrap does not assume the conclusion of pooling. The
retained singleton requests and norm/ceiling argument supply |B|>=2,
H odd and nonzero, x>=0 and q=(BH)^x. Thus q is1 or has absolute value
at least2, establishing q!=0,-1 before either pooled block is interpreted.
After pooling, M=q^x and B|M rule out x=0; the retained ratio then forces
x>=t. The later parent factorial and proof-flow interpretation can resume
with its required hypotheses.

The manuscript correctly describes private-witness existential
equivalence for reciprocal pooling. It does not claim that the rational
quotient restoration is a polynomial map on the ambient integer lattice.

## 4. Calibration and novelty wording are appropriately bounded

The retained files contain the named interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their displayed
statements have the claimed C222/ZF and ZF/ZFC endpoints. The manuscript
uses these as inherited dependencies and expressly distinguishes ordinary
mathematical formalizability in ZFC from a new encoded object-language
proof or a new complete Lean/Rocq build.

The work proves equivalences with syntactic consistency; it does not
assert the absence of solutions or prove either consistency or
inconsistency. The comparison with a37-integer quartic and the maintained
15-positive-variable display prevents the218/215 figures from being
misrepresented as absolute variable records. The larger support and
higher companion degree are explicitly disclosed.

The novelty claim is scoped to the inspected repository snapshot.
Inherited quadratic-projection methods are credited as inherited;
their application and the complete resulting coefficients are the new
endpoint. The different-base rational-sum argument is distinguished from
the parent's same-base divisibility pool and the older
reciprocal-factorial CRT mechanism. No literature-wide historical
priority or global simplicity minimum is claimed.

## 5. Remaining publication checks

The main mathematical text and its initial equation specifications pass
this review. The separately generated residual appendix must still be
checked against the coefficient JSON, and the final PDF must be rendered
and inspected. The final archive checker should include this review,
the frozen transformation data, the inherited source closure, and the
independent arithmetic checker. Those checks concern the final artifact
and are distinct from the mathematical conclusions above.
