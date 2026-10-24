# Final review of the logical source and arithmetic front end

## Scope and conclusion

This independent review covers the final article
`report/Batched_Pell_1873.tex`, particularly its numerical constructors,
C222 calibration, Horn-flow construction, beta trace, lifted CRT theorem,
arithmetic macro statements, domain restoration and exact consistency
claim. The final primary equation has 1,873 unrestricted integer
variables, 1,468 quadratic residuals and 77,523 quartic monomials.

No substantive mathematical flaw was found in these reviewed portions.
The simultaneous Pell and signed-index arguments received a separate
algebra review; the present conclusion does not substitute for that review.
The result is an ordinary mathematical proof formalizable in ZFC,
supported by exact finite artifact checks. It is not a newly emitted
end-to-end Lean certificate or an encoded object-language ZFC derivation.

## Constructor transcription and the applied correction

The printed constructors were compared with the pinned
`provenance/logical/Code254.lean` and
`provenance/logical/KCode222.lean`. The formulas for the implication,
relation, quantifier and equality codes, negation, existential
quantification, rho1 through rho6, the merged equality row G, rho8, req,
nks, vr and bundle agree with those definitions.

The first article draft's deeply nested display for `cl(a,b,k,m)` had
one extra closing parenthesis. This was a display transcription defect;
the authoritative JSON constructor and emitted polynomial were unchanged.
The final article replaces the display by the following balanced helpers:

    sb(a,b,k)   = Q(k,I(E(k,a),E(k,b)))
    c1(a,b,k,m) = Q(a,I(sb(a,b,k),req(b,k,m)))
    c2(a,b,k,m) = Q(a,I(m,N(c1(a,b,k,m))))
    cl(a,b,k,m) = Q(b,I(E(b,k),N(c2(a,b,k,m))))

Here `N` in this displayed code denotes the negation constructor, as in
the article's `\Neg`; it is unrelated to the proof-row horizon. The
review parsed the pinned Lean `clos` definition into an abstract syntax
tree and expanded these helper definitions. Their trees agree exactly,
not just at numerical examples. The helper block was confirmed in the
final article.

The bundle guard remains the exact natural existential condition

    ((c-a)(c-b))^2=(d+1)^2.

It holds for some natural d exactly when c differs from both a and b;
neither difference is required to be positive. The twelve branches have
the correct inventory: truth, nine axiom branches, modus ponens and
generalization, with unused premises padded by truth code zero.

## Horn flow, padding and the trace

Padding by truth rows can make the positive horizon N bound both the
length of a finite proof tree and every one of its four actual rule
parameters. This places no upper bound on possible refutations.
Monotonicity of the nonnegative constructor polynomials gives the stated
label bound H(N). The coefficient sum on the premise side is at most
`2(H+1)^(2N) <= 2^(2HN+1) = M0`, so the base `M=M0+1` is sufficient.

The least-nonzero-coefficient reduction proves that equality of the two
product evaluations implies equality of their polynomials. Their
distinct rational roots identify the positive-label multiplicities.
The nonderivable-label cut argument is valid for the fixed
single-conclusion rules and nonnegative multiplicities. Cycles,
self-loops, repeated premises and the truth padding do not invalidate it.

All accumulator factors are positive, and S0 is positive. Induction
therefore makes every accumulator value positive, justifying the
telescoping cancellation. This clarification was requested for the
article; it is a consequence of existing hypotheses, not an additional
condition on certificates.

The beta modulus argument is correct for indices zero through N because
y is a multiple of N! and exceeds every trace entry. The local bound
`S<=y<1+(i+1)y` proves the strict remainder bound. Uniqueness of the
remainder makes independently supplied adjacent row witnesses describe
one consistent common trace. The two endpoint equations select its
required beginning and ending values.

## Absolute bounds and the lifted CRT theorem

The signed local row and its nonnegative paired representation define
the same integer polynomial. Replacing subtraction by addition and
constants by their absolute values gives a valid monotone circuit
majorant by induction on the arithmetic graph.

For `L=Rplus(N,u)+N`, every prime divisor p of `1+(i+1)L!` exceeds L.
The falling-factorial identity converts a binomial divisibility into a
bounded root modulo p. The index congruence and the inequality
`|R(i,w)|<=Rplus(N,u)<=L<p` then force the decoded row to vanish as an
integer. The proof does not mistake a residue modulo a composite modulus
for a bounded coordinate.

The prime-power lifting in completeness correctly absorbs the valuations
of each range factorial before division. It also supplies sufficiently
large positive encoded columns. The unlifted-period shortcut is rightly
rejected: `15` divides `choose(0,5)` but not `choose(15,5)=3003`.
All strengthened periods occur only in the finite existence proof; no
prime-factorization operation remains in the emitted equation.

## Arithmetic macro and domain checks

The CRT product remainder formula is valid: modulo TQ-1 its numerator
equals the product of the desired affine moduli, and that positive
product lies strictly below the divisor.

The combined binomial graph gives the correct two Euclidean digit
bounds, including the case k>n. A negative high quotient would make its
nonnegative numerator negative, so omitting that quotient's separate
nonnegativity guard is sound. The factorial radius and ceiling quotient
match the supplied `FactorialRepresentation.lean` theorem. The positive
factorial output parameterization loses no witness.

Every power input is positive from the actual graph and the retained
domains before any power or factorial semantic equality is assumed.
The coordinate and index divisibility quotients recover their signs
from their natural numerators and the positive CRT product. The ordinary
division quotients recover their signs from a natural dividend, a
positive divisor and a strictly bounded natural remainder. These sign
restorations do not feed the power-input positivity proof.

The representation `x=a^2+b^2+c(c+1)` is nonnegative for every integer
triple, and represents every natural x by Legendre's three-square theorem
applied to 4x+1. Monic graph definitions and affine substitutions have
unique integral restoration. Squaring the quadratic residuals therefore
preserves the full existential zero set in the claimed integer domain.

## Exact logical strength and evidence boundary

The pinned declarations

    KEndpoint.c222_iff_zf_refutation
    ConstructibleChoice.zf_refutation_iff_zfc_refutation

are unconditional theorem statements in the supplied sources. In
particular their stated calibration requires no simulator, transition
table, machine coverage hypothesis or assumed halting behavior. Their
ordinary logical arguments are inherited dependencies, not new
consequences of the Pell batching theorem.

The report's chain from an integer zero to a finite syntactic ZFC
refutation has both existence directions. Its negation gives the
no-zero/Con(ZFC) consequence. The ordinary argument is conducted over
ZFC's internal natural numbers; it does not assume consistency,
arithmetic soundness, a standard model, or a finite refutation bound.
The wording is appropriately explicit that no new complete formal
proof object was produced.

## Reproduced source corruption controls

`verify_source_negative.py` imports only the independent `verify_source`
checker from the package, with standard-library support. It first checks
the unmodified final source and its temporary copy, then makes three
separate corruptions in a TemporaryDirectory:

1. Replace the first schema-parameter bound N by y.
2. Replace the absolute majorant by the signed encoded row.
3. Remove the nonnegativity requirement on the positive horizon's
   predecessor.

All three are rejected for their intended mathematical interface or
domain violation. The receipt in `checks/SOURCE_NEGATIVE_CONTROLS.json`
binds the current final source files and the independent checker by
SHA-256; it is not a receipt copied from an earlier graph. Normal Python
and optimized Python runs produce the same deterministic receipt. The
test does not import or run the polynomial builder and does not alter
any source or equation file.
