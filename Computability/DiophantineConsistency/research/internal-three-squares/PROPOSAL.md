# Proposal: Legendre's three-square theorem inside models of 𝗜𝚺₁

Status: proposal only, not started. It needs Vladimir's go-ahead because of its size.

## Why it is needed

Every remaining undominated point of the integer-row frontier has a `Pos` guard: packages 194,
153, 179, 132 (the 44/111 point) and 121, with 13–15 integer unknowns.

* The guard is `pos = 1 + p₁² + p₂² + p₃(p₃+1)`.
* Completeness (halting ⟹ integer zero) must represent the canonical budget as
  `budget = pos(p₁, p₂, p₃)`, that is `4·budget − 3 = (2p₁)² + (2p₂)² + (2p₃+1)²`.
* This must hold in every model `V` of `𝗜𝚺₁`, because the halting time, and hence `budget`,
  may be nonstandard (`IPRA_PROVABILITY_PLAN.md`, obstruction of 7 November 2026).
* Soundness is not affected.

The statement needed is the case `N ≡ 1 (mod 4)` of the theorem:

    ∀ N ≡ 1 (mod 4), ∃ a b c, N = (2a)² + (2b)² + (2c+1)²,

as a theorem about every `V ⊧ 𝗜𝚺₁`. Its parity form follows from the plain form: for `N ≡ 1
(mod 4)` exactly one of the three squares is odd.

## What exists

* **Neither Mathlib nor this tree has a three-square theorem**, even over ℕ (checked
  2026-11-11).
* **Mathlib has Dirichlet's theorem** (`Nat.forall_exists_prime_gt_and_eq_mod`, in
  `NumberTheory/LSeries/PrimesInAP`), but analytically and only over the standard ℕ. It is
  unusable inside a nonstandard model.
* **The tree has**, inside `𝗜𝚺₁`:
  * Pell existence (`ZRows.ModelPellExistence`);
  * coprime-square splitting (`ZRows.CoprimeSquares`);
  * `√` with `sqrt_spec_le` / `sqrt_spec_lt`;
  * gcd/CRT (`ZRows.GcdCRT`);
  * Fermat-type facts (`ZRows.ModelFermat`);
  * `Σ₁` induction and least-number principles;
  * the descent style of `P113Roots` (adjacent-coefficient descent).

## Routes

| Route | Ingredients inside 𝗜𝚺₁ | Main risk |
| --- | --- | --- |
| A. Ankeny / Mitchell | Dirichlet for the needed progressions; quadratic reciprocity (Jacobi symbols); Minkowski–Blichfeldt in dimension 3 | an **elementary** Dirichlet (Selberg/Shapiro style: characters, `L(1,χ) ≠ 0`) is a campaign of its own |
| B. Gauss (Disquisitiones, the ternary-form articles around Art. 288–293), Dirichlet-free | reduction of positive ternary forms of determinant 1 to `x²+y²+z²`; existence of a binary form of determinant `−N` in the required genus | the existence of genera, which Gauss proves through ternary forms, is long. Every step is finitary bounded arithmetic, which suits `𝗜𝚺₁` |
| C. Davenport–Cassels + rational representation | Euclidean descent for `x²+y²+z²` (rational ⟹ integral; close to existing descent code); then `N` is a sum of three rational squares | the rational step is Hasse–Minkowski for `x²+y²+z²−Nw²`, whose standard proofs again use Dirichlet |

Recommendation if approved: **route B, with C's descent as a lemma.** It avoids analytic number
theory entirely, and the ternary reduction is a finite descent of the kind already formalized
here.

Size, as a rough estimate for comparison only:
* ternary reduction: 8–12 modules;
* genus existence and reciprocity: 15–25 modules;
* the guard interface and the five completeness ports: 5–10 modules each.

That totals several thousand lines, larger than the P138 or Z10 campaigns.

## A cheaper possibility to rule out first

If the halted run is stationary, the halting time can be enlarged. That moves `N = 2341^(2T+4)`
and with it `budget`. Then completeness would only need **one** representable budget in that
family, not the general theorem, if the budget's polynomial form gives an explicit
decomposition for suitable `T`.

Examined 2026-11-11 for packages 132 and 194; it does not remove the obstruction:

* **132** (`lowdegree/PROOF.md` §§ 1, 7). `budget = Y² B0 − k² q⁸` with
  `B0 = k²(q² − Derr) − 4q²η²`.
  * In the canonical family `Y = M_bin/2` is fixed by the run, and so are `k`, `η` and `Derr`.
    The only freedom left is the halting time.
  * No identity writes `4·budget − 3` as three squares.
  * Forcing it, for example by choosing `T` to make `4·budget − 3` a prime `≡ 1 (mod 4)` (two
    squares by `ZRows.ModelFermat`), would need a prime-producing argument stronger than
    Dirichlet.
  * The package's own proof also uses the three-square theorem to restore its predecessor's guard
    (§ 6). A direct Lean soundness proof, as for 113, does not need that.
* **194** (`roots/PROOF.md` §§ 1, 5). The guard is `G = budget − [1 + p₂² + p₃(p₃+1)]`, but its
  completeness sets `G = p1_old²` (root extraction). So it needs the same
  `budget − 1 = p₁² + p₂² + p₃(p₃+1)`.

Packages 121, 153 and 179 have the same `Pos` form or inherit it. The general theorem, at least
for `N ≡ 1 (mod 4)`, is therefore required.
