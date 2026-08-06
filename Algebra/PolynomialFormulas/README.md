# Polynomial formulas and the Abel--Ruffini obstruction

This project gives Lean 4 and Rocq/Coq proofs of the classical formulas for
polynomial equations of degrees one through four, together with the usual
Abel--Ruffini obstruction in every degree at least five.  Lean additionally
proves the rootwise rational theorem: for every degree greater than four,
there is a polynomial over `Q` with exactly that degree and with no root
solvable by radicals.  The positive proofs are algebraic: they expand the
proposed values and kernel-check that the defining polynomial vanishes.

Radicals are represented by field elements together with the equations they
satisfy (`s² = D` for a square root and `u³ = z` for a cube root).  This keeps
analytic branch choices and root-existence facts out of the algebraic
correctness claim.  The Lean statements are generic over characteristic-zero
fields.  Most Coq statements are independently checked over the real numbers;
the exhaustive cubic theorem uses Coquelicot's complex field so that all three
roots and a genuine primitive cube root of unity are representable. In both
settings, algebraic tactics produce proof terms checked by the kernel.

The linear theorem proves uniqueness.  The quadratic development proves both
formula branches, their factorization, and that they exhaust every root.
The cubic development proves the Tschirnhaus translation to depressed form,
the compatible radical-pair identity in Cardano's formula, its discriminant
equation, and a three-linear-factor identity using a primitive cube root of
unity. The `cubic_eq_zero_iff` theorems prove that a value is a root exactly
when it occurs in the three-entry Cardano collection. The Coq development
includes a concrete complex primitive cube root, so this result is nonvacuous.
Ferrari's quartic development normalizes and depresses a general quartic,
proves the cubic-resolvent parameter equations imply a difference-of-squares
factorization, and uses quadratic exhaustiveness to prove the corresponding
`quartic_eq_zero_iff` theorem for all four entries.

Lean also supplies a coefficient-only specialization over the Gaussian
rationals `Q[I]`.  `GaussianPolynomialSolver.solve` accepts five coefficients
without assuming that the nominal quartic coefficient is nonzero.  It selects
the required square and cube radicals, returns genuine `RadicalExpression`
trees for every root, and dispatches through quartic, cubic, quadratic,
linear, and constant cases.  A nonzero constant returns an empty finite list;
the all-zero polynomial has a separate `identicallyZero` result.  The theorem
`solve_factorization` proves the exact ordered product, preserving repeated
roots, and `eval_eq_zero_iff_contains` proves soundness and exhaustiveness.

`GaussianQuinticSolver.solve` accepts one additional Gaussian-rational
coefficient.  If `a5 = 0`, its `lowerDegree` constructor delegates exactly to
the preceding degree-at-most-four result; `solve_factorization_of_a5_eq_zero` and
`eval_eq_zero_iff_contains_of_a5_eq_zero` inherit its complete correctness.
For `a5 ≠ 0`, it classically selects an invariant and radical certificate
package required by `LazardQuintic.solveGeneral`, if one exists.  Its
invariants are certified first over the Gaussian-rational coefficient field
and then embedded into the radical closure.  The five Lazard values are
noncomputably reified as `RadicalExpression` trees.  Because the present
Lazard certificate assumes nonzero denominators and therefore excludes
singular solvable inputs such as `X^5`, a missing Lazard package falls back to
a classically selected `CompleteRadicalSolution`, if one exists.  The finite
five-entry vectors are kept in distinct `lazardCandidates` and
`completeRadical` result constructors; `unsupported` is returned only when
neither package exists.  The genuine Lazard branch is deliberately not
accompanied by a correctness theorem: the Lazard
transcription's soundness and certificate-existence results remain future
work.

Every returned `ExplicitRadical` can additionally be passed to
`ExplicitRadical.boundingBox`.  For a rational `ε > 0`, it returns a rectangle
whose four endpoints are rational.  `boundingBox_spec` proves that the exact
complex value lies in the rectangle, that both coordinate intervals are
ordered, and that its width and height are at most `ε` (in fact both are
exactly `ε`).  The solver bridge theorems `returnedRoot_boundingBox_spec` and
`root_has_boundingBox` connect these enclosures to soundness and exhaustiveness
of the original polynomial solver.

Lean now also supplies a distinct, fully executable approximation API.
`GaussianPolynomialApproximation.approximations` accepts the same five
Gaussian-rational coefficients (so leading coefficients may be zero), a proof
that they are not all zero, and a rational `ε > 0`. It returns
`List.Vector GaussianRat d`, where `d` is the actual degree of the input.
A nonzero constant therefore returns the empty vector. Each entry is a
literal pair of rational real and imaginary coordinates.

The implementation normalizes the polynomial over `Q[I]`, searches for four
monic separable factor layers, and exhaustively enumerates exact rational
contraction-disk certificates. Repeated irreducible factors remain in separate
layers, so repeated roots retain their multiplicities. Every test performed
by the search is a finite Boolean test involving only natural numbers and
Gaussian-rational arithmetic. The analytic and factorization arguments prove
that a valid certificate exists and are used only as the erased termination
proof for `Nat.find`; no chosen complex root or real-number operation occurs
in the returned-data computation.

`GaussianPolynomialApproximation.approximations_correct` proves that there is
a position-matched list containing exactly the original polynomial's complex
root multiset and that the Manhattan distance from every returned Gaussian
rational to its corresponding exact root is at most `ε`. Thus soundness,
exhaustiveness, order matching, and multiplicity are all covered by one
theorem. The generic exhaustive search is a correctness-first implementation,
not an optimized numerical root finder; constant, linear, and small-integer
split quadratic/quartic inputs have fast seed certificates and are exercised
by native evaluation tests.

For the negative result, both developments use the explicit rational quintic

```text
X^5 - 4X + 2.
```

Lean imports mathlib's checked Galois-theoretic proof that none of this
quintic's complex roots belongs to the smallest field containing the rationals
and closed under field operations and nonzero-order radicals.  A local typed
syntax for rational constants, addition, subtraction, multiplication,
inversion, and chosen nth roots is proved exactly equivalent to membership in
that semantic closure.
Rocq imports the axiom-free [MathComp Abel development](https://github.com/math-comp/Abel),
whose `algterm` language includes the same field operations, powers, roots,
and roots of unity, and whose `solvable_formula` theorem equates complete root
representability in that language with solvability by radicals.  The local
Coq proof additionally shows that `algterm`-representability is preserved by
automorphisms of the algebraic closure and that all roots of the irreducible
quintic are conjugate.  Consequently every individual quintic root has no
radical expression; this strengthens the imported whole-root-set
contradiction without adding assumptions.

Multiplying the quintic by `X^(n-5)` retains every obstructed quintic root and
produces a monic polynomial of degree `n`.  Thus, for every `n >= 5`, the
formalizations exhibit a degree-`n` rational polynomial for which no complete
radical solution exists, and refute a universal complete radical solver at
that degree.  This is the standard scope of Abel--Ruffini: it does **not** say
that every polynomial of degree greater than four is unsolvable.  The word
"complete" is also essential here, because the padded polynomial has the easy
root zero in addition to its unsolvable quintic roots.

Lean's degree-exact rational construction uses the Selmer polynomial

```text
X^n - X - 1.
```

For every `n >= 5`, the formal proof establishes monicity, exact degree `n`,
and exactly `n` complex roots.  Selmer irreducibility, a reusable bound on the
only possible repeated residue root, and Morse's inertia criterion give a
surjection from the polynomial's Galois group onto the symmetric group on its
roots.  Since that symmetric group is not solvable, no complex root belongs to
`solvableByRad Q C`; equivalently, no root has a term in the local explicit
radical-expression syntax.  The public existential theorem is
`SelmerAbelRuffini.every_degree_gt_four_has_rational_polynomial_with_no_radical_root`.

Lean also contains an independent fixed-field construction.  Let

```text
L_n = Q(x_0, ..., x_(n-1))
K_n = L_n^(S_n),
```

where `S_n` permutes the independent variables, and take the orbit polynomial
of `x_0` over the fixed field `K_n`.  The proof identifies its `n` distinct
roots, proves that they generate `L_n`, and identifies its Galois group with
`S_n`.  For `n >= 5`, irreducibility and the nonsolvability of `S_n` imply
that **every** root lies outside `solvableByRad K_n L_n`.  The public theorem
is
`GenericAbelRuffini.every_degree_gt_four_has_polynomial_with_no_radical_root`.

This alternative theorem is over the symmetric rational-function coefficient
field `K_n`.  The Rocq/Coq development proves the rational quintic rootwise
theorem and the padded universal-formula obstruction above; it does not claim
either Lean's arbitrary-degree Selmer theorem or the generic fixed-field
construction.  The padding, rational all-roots, and generic all-roots theorems
therefore have deliberately distinct scopes.

## Deciding an individual integer quintic

The mathematical proof and implementation outline in
[`Decidability.md`](Decidability.md) show that it is recursive—in fact,
primitive recursive—to decide whether every root of a given
integer-coefficient quintic is expressible in radicals. The procedure
monicizes the polynomial, detects reducibility by enumerating bounded linear
and quadratic factors, and in the irreducible case applies the scalar
Frobenius--Dummit sextic and a bounded rational-root search.

Lean now formalizes this argument end to end. The checked development proves
completeness of the bounded factor search, handles the reducible branch using
the radical solvability of polynomials of degree at most four, constructs the
actual scalar Frobenius--Dummit resolvent, and formalizes the $F_{20}$ subgroup
classification and Chapman's repeated-resolvent-root correction. It then
specializes the resolvent coefficients by Vieta, proves the irreducible
Galois-group criterion and the bounded rational-root test, and assembles a
Boolean characteristic function for the all-complex-roots radical predicate.
The coefficient transformations and searches are proved primitive recursive;
the final theorems give `ComputablePred` and the existence of a
`PartrecToTM2` program satisfying the stated execution relation on encoded
integer quintics.

The seven elementary-symmetric coefficient polynomials are also present as a
302-term sparse table. A proved sparse-normalization procedure certifies the
table against the six scalar roots over every commutative ring, and Lean then
identifies the table with the abstract symmetric-polynomial construction.
Consequently the final Boolean is directly evaluable, in addition to being
proved primitive recursive. The four largest certificate reductions use
`native_decide` and therefore include Lean's native compiler/runtime in the
documented trust boundary; the remaining three use ordinary kernel `decide`.
No claim is made that the bounded implementation is optimized, or that the
existential `PartrecToTM2` code has been printed as a standalone extracted
solver.

Rocq independently verifies the same bounded coefficient procedure in
[`QuinticCanonicalDecision.v`](Coq/QuinticCanonicalDecision.v).
`quintic_radicalb` combines the complete bounded factor search with the
computed scalar Frobenius--Dummit resolvent, and `quintic_radicalP` reflects
the exact all-roots `algterm rat` predicate to that Boolean.  The earlier
[`QuinticRadicalDecidability.v`](Coq/QuinticRadicalDecidability.v) remains as
a separate semantic implementation through MathComp-Abel's abstract
splitting field and also supplies the natural-number-code reflector.

## Deciding an individual integer sextic

Lean also formalizes a recursive decision for exact degree-six integer
polynomials.  After integral monicization, a finite search for monic factors
of degrees one through three decides reducibility.  A nonlinear factor leaves
only factors of degree at most four; a linear factor reduces the question to
the verified quintic criterion.  On the irreducible branch, two separating
block-system resolvents of degrees fifteen and ten detect whether the Galois
group is solvable.  Their integer coefficients are computed from sparse
symmetric polynomials, and bounded rational-root searches decide the two
tests.

The separating parameters are obtained by a proved terminating unbounded
search.  Accordingly the assembled Boolean is proved `Computable`, rather
than `Primrec`.  The public results
`sexticRadicalDecision_correct`, `allRootsRadical_computablePred`, and
`has_verified_sextic_radical_turing_machine` respectively prove semantic
correctness, Mathlib recursive decidability, and existence of a verified
`PartrecToTM2` program.  Each computability fact is derived compositionally
from the definition of the function concerned; no function is marked
recursive by a kernel special case.

Rocq now verifies a direct recursive coefficient program for the same sextic
predicate.  The files named `SexticMuRec*.v` compile signed arithmetic,
integral monicization, bounded factor and rational-root searches, the quintic
branch, and the compact pair/triple collision evaluators to the explicit
`recalg` language from Coq-Library-Undecidability.  The separating parameters
are selected by genuine unbounded minimization after a proof that a successful
parameter exists.  Structural Newton, Möbius, mixed-radix, and homogeneous
evaluation lemmas connect those programs to the degree-fifteen and degree-ten
resolvents.

[`SexticMuRecVerifiedDecision.v`](Coq/SexticMuRecVerifiedDecision.v) exposes
parameter-free Booleans and recursive programs on both seven zigzag-coded
coefficients and a single natural-number encoding.  Its public graph theorems
`encoded_raw_sextic_radical_relation_murec` and
`encoded_raw_sextic_radical_code_relation_murec` prove `MuRec_computable`;
`encoded_raw_sextic_radical_decidable` and
`encoded_raw_sextic_radical_code_decidable` give the corresponding explicit
`{P} + {~ P}` decisions for the exact all-roots predicate.  The computational
endpoints are closed in the assumption audit.  The semantic reflectors use
only the already documented classical splitting-field bridge.

[`SexticRadicalDecidability.v`](Coq/SexticRadicalDecidability.v) remains as an
independent semantic decision through MathComp-Abel's abstract `numfield`.
The new `MuRec` development is the recursively verified coefficient route;
the older file is useful as a separate semantic cross-check.

## Formula interfaces and scope

The solver functions are ordinary reducible definitions.  For example, the
committed examples evaluate

```text
x² - 5x + 6  ->  (3, 2)
x⁴ - 5x² + 4 ->  (2, 1, -1, -2).
```

For degrees two through four, the function arguments include the square/cube
radicals used by the classical formulas.  Their correctness theorems require
the corresponding equations (`s² = D`, `u³ = z`, the Cardano branch-product
condition, the primitive cube-root equation `ω² + ω + 1 = 0`, and the Ferrari
resolvent equations).  This is intentional: a bare characteristic-zero field
does not provide total radical operations, and real numbers cannot represent
nonreal roots. Once certified radical values are supplied, the functions
compute fixed-size root collections; the biconditional theorems prove both
that every entry is correct and that every root occurs. No unproved radical
oracle or hidden branch convention is introduced.

The Gaussian-rational API removes those radical arguments from the caller.
It uses exact, decidable arithmetic in `QuadraticAlgebra Q (-1) 0` for all
coefficient-dependent branches, including Cardano's `p = 0` case, Ferrari's
`q = 0` case, and every zero leading coefficient.  Chosen roots in `C` use
the proved fundamental theorem of algebra and classical choice, and their
power equations are stored in the returned typed syntax.  Consequently this
API is a total noncomputable Lean function, not code-generatable numerical
software and not a kernel special case for radical operations. This statement
refers to `GaussianPolynomialSolver.solve`, which returns exact radical syntax;
the independent `GaussianPolynomialApproximation.approximations` function
described above is code-generatable and returns Gaussian rationals.

The rational bounding-box operation is likewise noncomputable: it applies
mathlib's noncomputable floor operation to the real and imaginary parts of the
exact complex value.  It is a fully proved mathematical enclosure function,
but it does not turn the opaque `Classical.choose` roots into printable
numerical approximations. The executable approximation API avoids evaluating
those opaque values: it searches coefficient-level rational contraction
certificates and proves afterward that their centers match every exact root.

## Checking

From the repository root:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +PolynomialFormulas

git submodule update --init lib/MathComp-Abel
opam install --yes --deps-only ./lib/MathComp-Abel/coq-mathcomp-abel.opam
Push-Location Algebra/PolynomialFormulas/Coq
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq

# Direct Mu-recursive sextic certificate (uses the pinned
# Coq-Library-Undecidability source tree).
rocq makefile -f _CoqProject.murec -o Makefile.murec
make -f Makefile.murec
Pop-Location
```

The Abel submodule is pinned to the Rocq-9-compatible upstream commit
`bce31b97c6f0897749dbd431754264373c22553e`; the `--deps-only` command installs
its compatible MathComp prerequisites while the local makefile compiles the
pinned proof source itself.  Its complete proof and formula-language
equivalence are described in the accompanying
[ITP 2021 paper](https://doi.org/10.4230/LIPIcs.ITP.2021.8).
The currently released `coq-mathcomp-real-closed` dependency supports Rocq
versions `>= 9.0, < 9.2`; this project is verified with Rocq `9.0.1`.
