# From supplied representation data to nine natural unknowns

[`EquationFromRep.lean`](Lean/DiophantineConsistency/EquationFromRep.lean)
combines the checked construction stages into one type-valued constructor:

```lean
EquationFromRep.construct (r : Rep Empty (fun _ => A))
```

Its result contains an `Expr (Fin 9)`, an actual
`MvPolynomial (Fin 9) ℤ`, equality of their values on every integer tuple,
and proofs that their natural solvability is equivalent to `A`. Thus their
lack of natural solutions is equivalent to `¬ A`.

The stages are:

1. [`QuarticCompiler`](QUARTIC_COMPILER.md) computes a normalized quartic
   from the supplied expression by quadratic gate residuals and a sum of
   squares. Its distinguished input is ignored.
2. [`JonesIndex.lean`](Lean/DiophantineConsistency/JonesIndex.lean) specifies
   the coding index by a finite coefficient sum, a power of two, and two
   polynomial evaluations. `index_correct` proves the required index
   conditions for these literal values.
3. [`NinePolynomial.lean`](Lean/DiophantineConsistency/NinePolynomial.lean)
   instantiates the existing Jones correctness theorem with these data.
   Fixing the input to `1` leaves nine natural unknowns.
4. [`JonesSyntax.lean`](Lean/DiophantineConsistency/JonesSyntax.lean)
   builds matching arithmetic syntax. Its relation combiner is the closed
   two-radicand formula proved in
   [`RefinedPair.lean`](Lean/DiophantineConsistency/RefinedPair.lean).

No construction stage selects a representing polynomial, an index, or a
final expression from a proposition-valued existence theorem. In
particular, these stages contain no `Classical.choose`. Their transitive
axiom audits report only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`; the library uses classical mathematics internally.

The `EquationFromRep.construct` wrapper uses imported polynomial coefficient
readers, univariate degree bounds, and polynomial evaluations, so that
particular mathematical constructor remains `noncomputable`.

[`ExecutableJones.lean`](Lean/DiophantineConsistency/ExecutableJones.lean)
provides a second, fully executable data path:

```lean
ExecutableJones.fromRep (r : Rep Empty (fun _ => A)) : Expr (Fin 9)
```

[`SyntaxCoefficients.lean`](Lean/DiophantineConsistency/SyntaxCoefficients.lean)
expands arithmetic syntax into a finite list of monomials, retaining
duplicates, and computes a coefficient by summing its matching terms.
The checked reader agrees with `MvPolynomial.coeff`.
[`QuarticSyntax.lean`](Lean/DiophantineConsistency/QuarticSyntax.lean)
emits the quartic sum of squares as executable syntax, using an explicit
index for the residual equations, and proves that it denotes the same
quartic as `QuarticCompiler`.

The executable Jones adapter computes the specified index `z,y` directly
from those coefficients. It emits the coding polynomials `e,l,λ` from
their defining finite sums. For the star sum it explicitly enumerates
bounded exponent vectors and retains those with sum four, avoiding a
choice of ordering for a `Finset`. All data definitions in this branch
are ordinary `def`s accepted by Lean's code compiler. No polynomial
coefficient reader, degree reader, or interpretation is called by the
executable function.

`ExecutableJones.fromRep_correct` proves natural solvability equivalent to
`A`; `noZero_fromRep` proves the corresponding no-solution statement.
`eval_fromRep_polynomial` proves agreement at every integer tuple with the
polynomial produced by the mathematical constructor. These are finite
algorithms and correctness results; the expanded syntax can be extremely
large, and no practical running-time claim is made.

The starting `Rep Empty (fun _ => A)` is an explicit input. An existential
MRDP theorem alone does not supply that input. Applying this constructor
to ZFC inconsistency requires a separate, checked construction of the
appropriate representation data; this file does not claim that bridge.
