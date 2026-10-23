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
coordinate renaming, conjunction, and finite existential blocks are checked
constructors. `Expr.toPolynomial` interprets the supplied expression as an
ordinary integer multivariate polynomial.

[ArithmeticRepresentation.lean](Lean/DiophantineConsistency/ArithmeticRepresentation.lean)
adds explicit graph representations and substitution of represented
functions into predicates. Constants, coordinates, addition, multiplication,
inequalities, divisibility, and modular congruence have explicit constructors,
including the zero-divisor and zero-modulus cases.

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
divisibility, and polynomial evaluation. Compiling all those operations into
explicit expression data remains work in progress.

The primitive-recursion compiler will use a data-valued syntax mirroring
`Nat.Primrec'`. The checked `MRDP.recursionTrace_iff` supplies its finite-trace
correctness argument. A narrow elaboration-time reifier may generate a
concrete program from the existing structural computability proof. Such a
tactic must emit data and a kernel-checked evaluation theorem, and fail on
unsupported proof forms.

## The Jones stage

[JonesIndex.lean](Lean/DiophantineConsistency/JonesIndex.lean) exports the
finite index recipe: sum the specified coefficient bounds, form the
specified power of two, and evaluate the two coding polynomials. Its
`Parameters` record contains those numbers and a proof of `Index`.
It does not choose an index from an existential theorem.

The nine-variable master theorem accepts any normalized quartic with at
least one witness. A direct gate-to-quartic compiler can therefore retain
its own finite witness count and avoid the 58-witness universal compression.
The final nine-variable expression and its two-radicand relation-combining
finalizer are being specified directly from their arithmetic formulas.

Some imported ordinary polynomial operations are marked `noncomputable`.
A choice-free finite mathematical recipe is therefore a different milestone
from an executable syntax compiler. The expression layer is intended to
establish the latter as well.

## Remaining integration

1. Explicit graph data for exponentiation and the remaining CRT arithmetic.
2. Data-valued bounded-universal and primitive-recursion compilers.
3. A concrete program for the actual refutation semidecider, with its
   evaluation theorem.
4. A normalized quartic and direct Jones finalization retaining all data.
5. A final evaluation equivalence with the syntactic ZFC endpoint.

Object-level ZFC formalization and numerical size comparisons remain
separate obligations. The existence-based external Lean equivalence is
already checked and documented in [STATUS.md](STATUS.md).
