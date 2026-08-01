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

The Rocq file
[`QuinticRadicalDecidability.v`](Coq/QuinticRadicalDecidability.v) provides an
independent kernel-checked semantic bridge. It reflects the exact all-roots
`algterm rat` predicate to a Boolean for degree-five integer polynomials and
their natural-number encodings. That reflector still uses MathComp-Abel's
opaque abstract splitting field; it is semantic rather than an extracted
implementation of the bounded coefficient procedure, and direct standard
extraction remains unavailable because of MathComp sort polymorphism.

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

The Rocq development has a deliberately narrower executable boundary.
[`SexticRecursiveCore.v`](Coq/SexticRecursiveCore.v) gives a transparent
Gallina monicization and bounded factor search, and
[`SexticFactorCompleteness.v`](Coq/SexticFactorCompleteness.v) proves that
search complete.  [`SexticRadicalDecidability.v`](Coq/SexticRadicalDecidability.v)
proves the exact all-roots proposition decidable in Coq's `{P} + {~ P}` sense
by reflecting it through MathComp-Abel.  That semantic Boolean uses the opaque
abstract `numfield` construction; unlike the Lean theorem, it is not claimed
to be an extracted or recursively verified coefficient program.  The theorem
names include `semantic` to prevent those two meanings of “decidable” from
being confused.

## Calculator interface and scope

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
