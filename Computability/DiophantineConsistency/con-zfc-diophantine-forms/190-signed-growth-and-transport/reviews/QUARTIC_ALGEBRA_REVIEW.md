# Independent internal review of the 209-variable algebraic reduction

Scope: `agent_direct/result/ALGEBRA_PROOF.md`, the literal builder
`code/build209.py`, the F64 coordinate certificate, and the F128 residual-basis
certificate. This review concerns the new algebra and its interface; it does
not replace the separately required signed-horizon/cofinal-witness proof or
the inherited numerical-calculus calibration. This is an AI-assisted internal
review, not external human peer review.

## Findings

No mathematical defect was found in the new algebraic reduction.

1. Replacing the old quadratic horizon by `t=2+4z` is correctly identified as
   a semantic change, not a polynomial isomorphism of the original system.
   Conditional on that semantic theorem, eliminating old t by the displayed
   affine substitution and renaming z gives the stated integer-zero bijection.
   The inverse restores t=2+4*x0 and old z=x0; all residuals remain quadratic.
2. Since `t=2(1+2z)`, t is nonzero and its exact 2-adic valuation is one for
   every integer z, including negative z. The retained row
   `F=2^19*t*(2u+1)` therefore gives exact valuation 20 for F. Dividing this
   coordinate by 64 or 128 is licensed at every zero. After the substitution,
   scalar normalization of the growth row is coefficientwise integral and
   preserves its zero set. The inverse is integral for precisely the stated
   reason; no ambient-lattice bijection is being asserted.
3. In the F128 companion, R135 remains fixed, and the two changes are
   `R98 <- R98+4*R135` and `R124 <- R124+6*R135`. Their inverse subtracts the
   same multiples. This is an invertible integer residual-basis change.
   It preserves the simultaneous zero set, hence the zero set of the sum of
   squares, while it need not preserve the polynomial's values elsewhere.
4. The claimed quartic coefficient at `x0^2*x208^2` follows directly from
   the normalized last growth row. Its cross coefficient is -65536 in F64
   and -32768 in F128, whose squares are 2^32 and 2^30. No other residual
   involves x208, so this coefficient cannot be canceled. It certifies exact
   degree four independently of naive degree propagation.
5. The global height and support claims are finite collected-polynomial
   metrics; I inspected the recorded metrics but did not duplicate the
   exhaustive coefficient verifier, as requested. The proof clearly
   distinguishes these computations from the semantic theorem.

## Semantic interface checked in advance

The source210 report explicitly retains a signed power request at base q with
exponent t. This is crucial: once the radix argument gives |q|>=2, it forces
t>=0 and hence t>=2. Before then, the growth row already implies nonzero even
F and |F|>=2^19|t|. The beta spacing y=F(2v+1) then has |y|>=|F|, and
|1+(t+1)y|>=|y|-1>1 because |t+1|>=1. Thus the terminal beta row excludes
x=0 without assuming a positive horizon. These observations support the
intended acyclic bootstrap; the final review should still inspect the full
cofinal-witness proof, especially the odd-binomial construction at v2(F)=20.

Reviewed source identities: incoming source210 equation SHA-256
`20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a`,
F64 equation SHA-256
`b0506067c482b5e695d4ed353f08381e030728e0c088b2e56f3d00329e169fe1`,
and F128-basis equation SHA-256
`d77c026dd5b24bbd06512078403a5becac10beac7a6e28831e897d36a9d8d886`.
