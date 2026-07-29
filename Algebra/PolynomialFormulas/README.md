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
