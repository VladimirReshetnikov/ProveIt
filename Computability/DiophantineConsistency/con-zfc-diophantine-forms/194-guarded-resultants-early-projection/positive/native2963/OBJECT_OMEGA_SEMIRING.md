# Polynomial arithmetic over every model's internal omega

`ObjectOmegaSemiring.Natural H` is the subtype of all elements of the omega
of a supplied `ZFAxioms` model. It is now a nontrivial `CommSemiring`.
Its addition and multiplication have exactly the existing `AddRel` and
`MulRel` graphs. Natural-number casts quote `natV` exactly.

The laws come from the checked definable-induction proofs in
`ObjectAdditionLaws`, `ObjectAdditionCancellation`, `ObjectMultiplicationLaws`
and `ObjectDistributivity`. The multiplicative identity has its own supplied
formula induction. Operations are semantic interpretations: multiplication
uses the proved total, unique graph. This does not choose executable
polynomial or compiler data from an existence proposition.

`NaturalExpressionSemiring` interprets finite supplied `NatExpr` syntax over
any semiring. It agrees with the original natural evaluator and, over a
commutative semiring, with evaluation of its actual natural-coefficient
`MvPolynomial`.

`ObjectNaturalSemiring` proves the exact connection to object formulas:

- `evalRel_iff` equates internal relational evaluation with evaluation in
  this semiring;
- `equationRel_iff` interprets an integer expression as equality of its two
  supplied natural-expression components;
- `sat_noZeroForm_iff` says that the actual no-zero sentence is satisfied
  precisely when those components differ at every internal natural tuple.

The tuples include nonstandard elements. They are never decoded as external
Lean natural numbers. Structural induction is on the finite supplied
expression syntax, and earlier inductions on internal naturals each use
an explicit definable formula.

The dedicated check applies the ring tactic to arbitrary internal values
and derives an actual ZFC no-zero proof for the constant-one expression.
These exercise the algebra and formula bridges together. Seventeen public
dependency audits use only the standard Lean axioms.

This permits finite polynomial identities to be interpreted uniformly in
every model. It supplies neither unrestricted external induction on this
carrier nor a transfer principle for arbitrary Lean theorems about `Nat`.
Arithmetic coding, representation correctness on nonstandard inputs and
the consistency/unsolvability biconditional remain separate obligations.
