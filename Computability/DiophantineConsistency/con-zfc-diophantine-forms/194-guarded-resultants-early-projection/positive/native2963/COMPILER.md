# Constructing the coefficient data

The initial nine-variable milestone uses `Classical.choose` on the proved
MRDP/Jones representation. The second route retains arithmetic data
throughout and now supplies the closed executable equation in
[`ExplicitZFC.lean`](Lean/DiophantineConsistency/ExplicitZFC.lean).
This document tracks its construction. None of the compiler pieces below decides consistency or
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

[`NaturalSimplifier.lean`](Lean/DiophantineConsistency/NaturalSimplifier.lean)
then folds constants and removes zero/unit operations in the two natural
expressions produced by signed splitting. Its value theorem holds for all
natural assignments, and its size theorem counts the exact wires used by
the quartic compiler.
[`SimplifiedJones.lean`](Lean/DiophantineConsistency/SimplifiedJones.lean)
uses these reduced expressions throughout the quartic/Jones construction.
Lean proves that its source witness count and positional exponent parameter
cannot increase, and proves the complete final solvability equivalence.
For the trivial equality `0 = 0`, this reduces seven source witness slots
to three, and the coding parameter from 390625 to 625. These examples check
the actual compiler counts, not estimates from a separate cost model.

[`WitnessCompaction.lean`](Lean/DiophantineConsistency/WitnessCompaction.lean)
then packs only the source coordinates that still occur in the simplified
natural pair. Executable occurrence lists and deduplication supply the new
index; unused values can be filled with zero. Lean proves preservation of
existential solvability and that the number retained is at most the original
witness count.
[`CompactedJones.lean`](Lean/DiophantineConsistency/CompactedJones.lean)
uses this source without changing its gate counts, proves a further
nonincreasing quartic witness count and Jones exponent parameter, and gives
the final equation currently selected by `ExplicitZFC`.

[`ComputationRepresentation.lean`](Lean/DiophantineConsistency/ComputationRepresentation.lean)
turns a supplied unary graph into a closed representation of attaining a
fixed accepted value. Construction of this expression performs no search.

`Computability.haltingTest` is the scalar bounded test for the literal
six-register refutation enumerator. Its result is one at some bound exactly
when ZFC has a finite refutation, as checked by
`exists_haltingTest_eq_one_iff_refutation` in `Bridge.lean`.
[`ZFCFromProgram.lean`](Lean/DiophantineConsistency/ZFCFromProgram.lean)
assembles the compiler and Jones stages from a supplied
`ScalarPRCode.Realizes haltingTest`.
[`DirectEnumerator.program`](DIRECT_PROGRAM.md) now supplies that input
directly from the arithmetic source; `ExplicitZFC` instantiates the whole
construction without any supplied-data hypotheses.

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

## Further reductions

The concrete refutation program and closed equation are now checked. Further
work includes further sharing of repeated code, replacing
the exponential-position Jones source by direct quadratic coding, and
measuring practical coefficient-generation costs. The generic proof reifier
is an optional tool; the closed equation uses directly constructed code.

[`DirectGraphEnumerator`](DIRECT_GRAPH.md) additionally represents the
arithmetic source directly, using quadratic Cantor graphs and explicit
equality branches. `NativeZFC` closes that second route without requiring a
generic scalar-program graph compilation. Its full numerical size comparison
has not been measured.

`SidonPositions.lean` supplies a checked foundation for a future direct
quadratic coding stage. The explicit weights `(2*m^2+1)*i+i^2`, including
index zero, have unique unordered pair sums. Their maximum is exactly
`2*m^3+m^2+m`, with a proved cubic bound. This does not yet replace the
Jones coding theorem in the closed equations.

`QuadraticCoding.lean` now proves the associated coefficient-extraction
identity over every commutative coefficient ring: the square of the encoded
coordinate polynomial gives diagonal coefficients `u_i^2` and off-diagonal
coefficients `2*u_i*u_j`. A complementary polynomial therefore extracts
twice the value of any supplied quadratic at the cubic-size target position.
This is a checked arithmetic foundation, not a completed change to the
nine-variable correctness theorem.

`PolynomialGraph.lean` supplies another arithmetic constructor: a supplied
natural polynomial, or one divided by a fixed positive denominator, has a
graph with zero additional witnesses. The denominator is cleared in its
single integer residual. Fixed-denominator polynomial data are closed under
addition, multiplication, and the source's Cantor pairing. These APIs retain
explicit coefficients and do not select a representation from an existence
proof.

`DirectComposition.lean` retains a graph's exposed output when substituting
its inputs. Its exact count theorem proves that every finite composition
uses one fewer witness than `GraphRep.compose`, including functions with no
inputs. The native formula blocks now use this constructor. See
[NATIVE_FORMULAS.md](NATIVE_FORMULAS.md) for the checked reduction of the
enumerator-step graph from 6,924 witnesses through 1,811 to 1,742. The latest
step uses one natural slack for integer disequality and a single nonzero
product to test the two gate alternatives.

All checked components are covered by
[`checks/CompilerAxioms.lean`](Lean/checks/CompilerAxioms.lean). Its audit
reports only the standard `propext`, `Classical.choice`, and `Quot.sound`.

Object-level ZFC formalization and numerical size comparisons remain
separate obligations. The existence-based external Lean equivalence is
already checked and documented in [STATUS.md](STATUS.md).
The actual object-language ZFC arithmetic foundation and remaining gaps are
documented in [OBJECT_ZFC.md](OBJECT_ZFC.md).
