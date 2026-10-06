# Proposed Lean integration

## Status

This is an implementation plan, not verified Lean source. No code in this package asserts that a Lean build was performed. The mathematical proofs appear in the article.

The relevant repository snapshot is `9ea383e9b28d885a936d5d681cd5584fffd2cb29`, under `Combinatorics/Ramsey/Lean/GowersSzemeredi`.

## Source interfaces inspected

`Sections14_15.lean` defines `HasProductProperty`, `AxisCube`, `GeneralArrangement`, `respectedCubePairCount`, and `respectedGeneralArrangementCount`. Its comments explicitly repair the gamma exponent of Corollary 14.6 and Lemma 14.8.

`Proofs14HigherArrangements.lean` has private helpers including:

- `cor147Phase`
- `cor147_moment_eq_count`
- `cor147_second_moment_le`
- `cor147_interpolation`
- `cor147_moment_interpolation`

It exposes `lemma_14_7_holds`. A client module cannot simply assume the private helpers are public. Export a suitable wrapper or move the appropriate definitions and proof to a public supporting module.

`Proofs14Arrangements.lean` constructs the reference-cube argument for Corollary 14.6. It explicitly notes that adjoining the reference base makes its auxiliary map injective. The refactor must preserve that multiplicity accounting.

`Proofs14ProductToArrangements.lean` defines theta with gamma exponent `3 * k * 4 ^ (k + 1)` and proves the corrected Lemma 14.8 with gamma exponent `21 * k * 4 ^ (k + 1)`.

## Proposed theorem sequence

### 1. Public all-moment counting lemma

State and prove, for each natural d >= 1,

    sum_(h,u,r) |Fourier(phase_(h,u))(r)|^(2d)
      = N^2 * respectedGeneralArrangementCount d B phi.

Reuse the existing finite index equivalences and orthogonality proof. The sign convention for the article's mixed derivative differs from the repository's by the fixed sign (-1)^k, which preserves every relevant additive relation.

### 2. Division-free amplification

Use the existing count with d=1 as the collision parameter. Over real casts prove

    (R 2)^(d-1) <= (R 1)^(d-2) * R d,   d >= 2.

Keep the zero case explicit. Do not start with inverse powers of R 1. At d=2, this is an identity; the equality-case argument requires d>=3.

### 3. Cubic collision cap

Define fibre sizes b_x. Establish the identity between R 1 and the sum of fixed-fibre respected cube-pair counts. Forget the label condition and inject

    (h,y,z) -> (y,y+h,z).

Recover the original ambient second-moment bound from C <= sum_x b_x^3 <= N^(3k+1). Preserve the cubic sum in a stronger public theorem.

### 4. Collision-parametrized product step

For each fixed side vector h prove

    R_2(h) >= gamma^(8 * 2^k) * C_h^4 / (N * (N^k)^4).

The reference-cube weight sums EXACTLY to C_h after summing over the reference base and vertical coordinate. Average over the N^k reference bases instead of claiming an injective map that forgets this base. Sum over h and apply the fourth-power mean inequality to obtain

    R_2 >= gamma^(8 * 2^k) * C^4 / N^(7k+1).

For formalization, a division-free version is preferable:

    gamma^(8 * 2^k) * C^4 <= N^(7k+1) * R_2.

### 5. Couple first; eliminate chi second

The normalized algebra is

    a_d >= a_2^(d-1)/chi^(d-2)
        >= gamma^(8*(d-1)*2^k) * chi^(3d-2).

Only NOW insert the collision lower bound

    chi >= beta^(4^k) * gamma^(2*k*4^k).

Inserting a lower bound directly into an inverse power of chi would reverse the needed inequality. This direction issue is the central algebraic obligation.

Retain the exact exponent `2*k*4^(k+1) + 8*2^k` in the pair theorem. Do not silently use the unsupported smaller printed exponent. Recover the safe catalogue theorem afterward.

### 6. Geometry and equality in independent modules

The finite stability proof requires only cardinalities, translation overlap, the small-difference-set lemma, and coordinate projections. It can be formalized independently of character theory.

For the joint equality theorem, separate:

1. equality in weighted moment interpolation;
2. classification of nonnegative measures with flat nonzero Fourier magnitudes;
3. exact Cartesian collision equality;
4. the common-mass argument using the zero side;
5. the graph-of-a-homomorphism description in the vertical coordinate.

Retain the arbitrary fibre translates c_x and arbitrary coordinate-omitting label terms. Neither can be removed from the normal form.

## Audit boundaries

These additions would prove stronger local statements. They would not, by themselves, verify the later extraction steps, the higher-dimensional induction, or the final density-increment iteration. Each new result should be checked and recorded on its own terms. Mathematical proof, source-statement fidelity, and Lean compilation are three distinct checks.
