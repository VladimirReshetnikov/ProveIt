# Constructing the coefficient data

The checked nine-variable milestone uses `Classical.choose` on the proved
MRDP/Jones representation. To obtain an explicit equation, we must keep its
arithmetic data throughout the construction. This document tracks that
second route. None of the compiler pieces below decides consistency or
searches for a refutation while choosing coefficients.

## Data and certificates

[Representation.lean](Lean/DiophantineConsistency/Representation.lean)
defines `Expr σ`, executable integer arithmetic syntax, and `Rep σ P`,
which contains a finite witness count, an expression over input and witness
coordinates, and a theorem that its zero set represents `P`.

Both structures live in `Type`. Their constructors supply data directly;
their theorem fields verify those data. They do not eliminate an arbitrary
proof of `Dioph`, `IsPoly`, or `REPred` into computational data. Equality,
coordinate renaming, conjunction, disjunction, and finite existential blocks are checked
constructors. `Expr.toPolynomial` interprets the supplied expression as an
ordinary integer multivariate polynomial.

[ArithmeticRepresentation.lean](Lean/DiophantineConsistency/ArithmeticRepresentation.lean)
adds explicit graph representations and substitution of represented
functions into predicates. Constants, coordinates, addition, multiplication,
inequalities, divisibility, and modular congruence have explicit constructors,
including the zero-divisor and zero-modulus cases.

[`ComposeRepresentation.lean`](Lean/DiophantineConsistency/ComposeRepresentation.lean)
adds finite conjunction and composition. The additional graph constructors
are checked for truncated subtraction, division, remainder, natural pairing,
and both inverse-pairing projections. The division and remainder graphs
include their zero-divisor conventions.

[`PellRepresentation.lean`](Lean/DiophantineConsistency/PellRepresentation.lean)
supplies the finite Matiyasevich certificate for the indexed Pell sequence.
[`PowerRepresentation.lean`](Lean/DiophantineConsistency/PowerRepresentation.lean)
then supplies exponentiation. Finally,
[`FactorialRepresentation.lean`](Lean/DiophantineConsistency/FactorialRepresentation.lean)
supplies binomial coefficients and factorials using base-digit and ceiling
identities, including `k > n` and `n = 0`. These are supplied expression
constructors, rather than applications of a proposition-valued MRDP theorem.

[NaturalExpression.lean](Lean/DiophantineConsistency/NaturalExpression.lean)
splits each integer expression into two natural-coefficient expressions.
Their difference is exactly its original value. This adds no witnesses and
supplies the natural equality required by the CRT argument. Natural
expression evaluation also compiles to the checked graph constructors.

## Bounded quantification and recursion

[BoundedForallCertificate.lean](Lean/DiophantineConsistency/BoundedForallCertificate.lean)
exposes the CRT certificate used locally in `MRDP.boundedForall_dioph`.
Its inputs are the two supplied natural polynomials; no representation is
chosen from a proposition. Both encoding and decoding are proved for every
bound, including zero. The certificate uses factorials, binomial coefficients,
divisibility, and polynomial evaluation.

[`BoundedForallRepresentation.lean`](Lean/DiophantineConsistency/BoundedForallRepresentation.lean)
now compiles that certificate into expression data. The checked API is
`Rep.boundedForall`: a supplied representation of `P(k,x)` produces one
representing `∀ k < x(b), P(k,x)`, including bound zero. Its construction
uses the explicit arithmetic graphs above, finite conjunctions, and finite
existential blocks. Polynomial interpretations occur in the correctness
proof; no polynomial representation is selected while constructing the data.

[`PRCode.lean`](Lean/DiophantineConsistency/PRCode.lean) and
[`ScalarPRCode.lean`](Lean/DiophantineConsistency/ScalarPRCode.lean) give
data-valued syntax mirroring `Nat.Primrec'` and `Nat.Primrec`, with executable
evaluation and checked computability proofs. The scalar syntax retains
pairing and its inverse projections as primitive instructions.
[`ScalarPRRepresentation.lean`](Lean/DiophantineConsistency/ScalarPRRepresentation.lean)
now supplies its complete graph compiler, by structural recursion over all
seven constructors. The recursion case uses `MRDP.recursionTrace_iff` and
the bounded-universal constructor to constrain every transition of an
explicit two-parameter beta-function trace.
A narrow elaboration-time reifier is being
tested on the actual bounded refutation test; it must emit data and a
kernel-checked evaluation theorem, and fail on unsupported proof forms.

[`ScalarPROptimizer.lean`](Lean/DiophantineConsistency/ScalarPROptimizer.lean)
supplies a separate certified simplifier before graph compilation. It removes
redundant projection/composition instructions and several trivial recursions.
Lean proves equality of evaluation at every natural input and that the
instruction-tree size never increases. For example, a recursive counter
with seven instructions becomes the single right inverse-pairing projection,
eliminating the need to encode its recursion trace. This is a program-size
bound; no general bound on the resulting Jones coefficient sizes is inferred.

[`ComputationRepresentation.lean`](Lean/DiophantineConsistency/ComputationRepresentation.lean)
turns a supplied unary graph into a closed representation of attaining a
fixed accepted value. Construction of this expression performs no search.

`Computability.haltingTest` is the scalar bounded test for the literal
six-register refutation enumerator. Its result is one at some bound exactly
when ZFC has a finite refutation, as checked by
`exists_haltingTest_eq_one_iff_refutation` in `Bridge.lean`.
[`ZFCFromProgram.lean`](Lean/DiophantineConsistency/ZFCFromProgram.lean)
assembles the compiler and Jones stages from a supplied
`ScalarPRCode.Realizes haltingTest`. Producing that concrete program data
remains a required input, not an assumption that the file conceals.

## The Jones stage

[JonesIndex.lean](Lean/DiophantineConsistency/JonesIndex.lean) exports the
finite index recipe: sum the specified coefficient bounds, form the
specified power of two, and evaluate the two coding polynomials. Its
`Parameters` record contains those numbers and a proof of `Index`.
It does not choose an index from an existential theorem.

The nine-variable master theorem accepts any normalized quartic with at
least one witness. The checked
[`QuarticCompiler`](QUARTIC_COMPILER.md) constructs one directly from a
supplied `Rep Empty`, retaining its finite witness count and avoiding the
58-witness universal compression. `NinePolynomial`, `RefinedPair`, and
`JonesSyntax` give the final polynomial and matching arithmetic syntax.

[`EquationFromRep`](COMPILER_JONES.md) now composes all these stages. Its
result contains a specified nine-variable equation, syntax/polynomial
evaluation equality on every integer tuple, and both natural-solvability
and unsolvability equivalences for the supplied predicate. No stage selects
an equation or index from a proposition-valued existence theorem.

The imported ordinary polynomial operations in that mathematical wrapper
are marked `noncomputable`. The second branch,
[`ExecutableJones.fromRep`](COMPILER_JONES.md), now replaces every such
data operation with finite syntax arithmetic: sparse coefficient expansion,
an explicit residual index, and explicit enumeration of the coding sums.
It is accepted by Lean as an ordinary executable `def`. Its values agree
with the specified polynomial on every integer tuple, and its natural
solvability is equivalent to the supplied predicate. This establishes an
executable compiler from supplied representation data; practical expansion
of the resulting very large syntax is a separate question.

## Remaining integration

1. A concrete program for the actual refutation semidecider, with its
   evaluation theorem.
2. Instantiate the program-to-ZFC constructor with the actual extracted
   program and audit the resulting closed equation.

All checked components are covered by
[`checks/CompilerAxioms.lean`](Lean/checks/CompilerAxioms.lean). Its audit
reports only the standard `propext`, `Classical.choice`, and `Quot.sound`.

Object-level ZFC formalization and numerical size comparisons remain
separate obligations. The existence-based external Lean equivalence is
already checked and documented in [STATUS.md](STATUS.md).
