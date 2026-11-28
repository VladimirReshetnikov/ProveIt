import Lib.General.Analysis.FiniteFourier
import Lib.General.LinearAlgebra.IntegralLattices

/-!
# Functions of positive type and singular minors

A function `Θ` on a finite group `G` is of positive type if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for some
vectors `u a` of a complex inner product space.

Notions from other files:

* `New.invTransposeGL` is the automorphism `g ↦ (gᵀ)⁻¹` of `GL n R`.

## Main definitions and results

* `New.card_mul_sum_det_eq_zero_le`: let `k` be a field with `q` elements, `π` a representation by
  `n × n` matrices over `k`, `A₀` and `A₁` two `n × m` matrices and `Θ ≥ 0` of positive type.
  Suppose that, for `v ≠ 0`, the stabilisers of `A₀ v` under `π` and of `A₁ v` under the
  contragredient of `π` have `Θ`-mass at most `Y ≥ 0`. Then the set where `det (A₁ᵀ π(s) A₀)`
  vanishes has mass at most `(2 Θ(G) + q ^ (|m| + |n| / 2) Y) / q`. The proof counts kernel
  vectors with additive characters and bounds the resulting inner product by a squared distance.

## Relation to the literature

See `New.Spanning.Unfolding.Moments` for related work.
-/

open scoped BigOperators
open InnerProductSpace Finset EuclideanSpace Complex Matrix WithLp Fintype AddChar

namespace New

variable {G H k n m : Type*} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Field k] [Fintype n] [DecidableEq n] [Fintype m] {u : G → H}

/-- If the inner product of two families of vectors indexed by a finite group `G` has the form
`⟪u a, v b⟫ = f (a⁻¹ * b)`, then `⟪∑ a, u a, ∑ a, v a⟫ = |G| · ∑ s, f s`. -/
lemma inner_sum_sum_eq_card_mul {v : G → H} (f : G → ℂ)
    (h : ∀ a b : G, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) :
    ⟪∑ a : G, u a, ∑ a : G, v a⟫_ℂ = Fintype.card G * ∑ s : G, f s := by
  -- For each `a` the map `b ↦ a⁻¹ * b` is a bijection of `G`.
  have h_row (a : G) := (Group.mulLeft_bijective a⁻¹).sum_comp f
  rw [sum_inner]
  simp [inner_sum, h, h_row]

/-- Let `Θ` be of positive type, `Θ (a⁻¹ * b) = ⟪u a, u b⟫`, let `ρ` be a matrix representation of
`G`, and let `c` be an orthonormal family indexed by the vectors of `kⁿ`. Then the squared norm of
`∑ a, c (ρ a x) ⊗ u a` is `|G|` times the sum of `Θ` over the `s` with `ρ s` fixing `x`. -/
lemma norm_sq_sum_tmul_eq_card_mul_sum [DecidableEq k] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* GL n k) {Θ : G → ℝ}
    (hu : ∀ a b : G, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) {c : (n → k) → E} (hc : Orthonormal ℂ c)
    (x : n → k) :
    ‖∑ a : G, c (ρ a • x) ⊗ₜ[ℂ] u a‖ ^ 2 = Fintype.card G * ∑ s : G with x = ρ s • x, Θ s := by
  let f (s : G) : ℝ := if x = ρ s • x then Θ s else 0
  have h_inner (a b : G) :
      ⟪c (ρ a • x) ⊗ₜ[ℂ] u a, c (ρ b • x) ⊗ₜ[ℂ] u b⟫_ℂ = f (a⁻¹ * b) := by
    simp [f, hu, orthonormal_iff_ite.1 hc, apply_ite ofReal, mul_smul, eq_inv_smul_iff]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sum_sum_eq_card_mul (fun s ↦ f s) h_inner, sum_filter]
  simp [f]

/-- For a primitive additive character `ψ` of a finite field with `q` elements, the functions
`ζ ↦ ψ (-x ⬝ᵥ ζ) / √(q ^ |n|)`, one for each `x : kⁿ`, are orthonormal. -/
lemma orthonormal_addChar_div_sqrt [Fintype k] [DecidableEq k] {ψ : AddChar k ℂ}
    (hψ : ψ.IsPrimitive) :
    Orthonormal ℂ fun x : n → k ↦ (toLp 2 fun ζ : n → k ↦
      ψ (-x ⬝ᵥ ζ) / √((Fintype.card k : ℝ) ^ Fintype.card n) : EuclideanSpace ℂ (n → k)) := by
  rw [orthonormal_iff_ite]
  intro x y
  -- Subtract the frequencies, then apply character orthogonality.
  have h_mul (ζ : n → k) :
      ψ (-(y ⬝ᵥ ζ)) * starRingEnd ℂ (ψ (-(x ⬝ᵥ ζ))) = ψ ((x - y) ⬝ᵥ ζ) := by
    rw [← map_neg_eq_conj, ← map_add_eq_mul, sub_dotProduct, neg_neg, neg_add_eq_sub]
  simp [PiLp.inner_apply, div_mul_div_comm, ← ofReal_mul, ← sum_div, h_mul,
    sum_addChar_dotProduct hψ, sub_eq_zero, -sub_dotProduct, ite_div]

/-- Let `π` be a representation of `G` by `n × n` matrices over a field with `q` elements, `π' s`
the inverse transpose of `π s`, `ψ` a primitive additive character, and `Θ` of positive type,
`Θ (a⁻¹ * b) = ⟪u a, u b⟫`. If the `Θ`-mass of the stabiliser of `x` under `π'` and that of
`z` under `π` are at most `Y`, then `Re ∑ s, ψ (x ⬝ᵥ π(s) z) Θ s ≤ q ^ (|n| / 2) Y`. -/
lemma re_sum_addChar_dotProduct_mul_le [Fintype k] [DecidableEq k] {ψ : AddChar k ℂ}
    (hψ : ψ.IsPrimitive) (π : G →* GL n k) {Θ : G → ℝ}
    (hu : ∀ a b : G, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) {x z : n → k} {Y : ℝ}
    (hx : ∑ s : G with x = invTransposeGL (π s) • x, Θ s ≤ Y)
    (hz : ∑ s : G with z = π s • z, Θ s ≤ Y) :
    (∑ s : G, ψ (x ⬝ᵥ (π s • z)) * Θ s).re ≤
      √((Fintype.card k : ℝ) ^ Fintype.card n) * Y := by
  -- Up to the factor `r / |G|` the sum is an inner product `⟪X₁, X₀⟫`, and
  -- the squared distance between these vectors bounds its real part by their mean squared norm.
  set r : ℝ := √((card k : ℝ) ^ card n)
  let π' : G →* GL n k := invTransposeGL.toMonoidHom.comp π
  let c (v : n → k) : EuclideanSpace ℂ (n → k) := toLp 2 fun ζ ↦ ψ (-v ⬝ᵥ ζ) / r
  let e (v : n → k) : EuclideanSpace ℂ (n → k) := EuclideanSpace.single v 1
  let X₁ : TensorProduct ℂ (EuclideanSpace ℂ (n → k)) H := ∑ a, c (π' a • x) ⊗ₜ[ℂ] u a
  let X₀ : TensorProduct ℂ (EuclideanSpace ℂ (n → k)) H := ∑ a, e (π a • z) ⊗ₜ[ℂ] u a
  let w (s : G) : ℂ := ψ (x ⬝ᵥ (π s • z)) * Θ s / r
  have h_dot (a b : G) : (π' a • x) ⬝ᵥ (π b • z) = x ⬝ᵥ π (a⁻¹ * b) • z := by
    simp [π', invTransposeGL, transposeGL, Units.smul_def, mulVec_transpose, dotProduct_mulVec,
      vecMul_vecMul]
  have h_inner (a b : G) :
      ⟪c (π' a • x) ⊗ₜ[ℂ] u a, e (π b • z) ⊗ₜ[ℂ] u b⟫_ℂ = w (a⁻¹ * b) := by
    simp [c, e, w, hu, EuclideanSpace.inner_single_right, ← map_neg_eq_conj, h_dot,
      div_mul_eq_mul_div, -map_mul]
  have h_X : ⟪X₁, X₀⟫_ℂ = card G * ∑ s, w s := inner_sum_sum_eq_card_mul w h_inner
  have hX₁ : ‖X₁‖ ^ 2 ≤ card G * Y :=
    (norm_sq_sum_tmul_eq_card_mul_sum π' hu (orthonormal_addChar_div_sqrt hψ) x).trans_le
      (by gcongr; exact hx)
  have hX₀ : ‖X₀‖ ^ 2 ≤ card G * Y :=
    (norm_sq_sum_tmul_eq_card_mul_sum π hu orthonormal_single z).trans_le (by gcongr)
  have h_cs : (⟪X₁, X₀⟫_ℂ).re ≤ card G * Y := by
    have hd : ‖X₁ - X₀‖ ^ 2 = ‖X₁‖ ^ 2 - 2 * (⟪X₁, X₀⟫_ℂ).re + ‖X₀‖ ^ 2 :=
      norm_sub_sq (𝕜 := ℂ) X₁ X₀
    linarith [sq_nonneg ‖X₁ - X₀‖]
  have hr_pos : 0 < r := by positivity
  calc (∑ s, ψ (x ⬝ᵥ (π s • z)) * Θ s).re
      = r * ((⟪X₁, X₀⟫_ℂ).re / card G) := by simp [h_X, w, ← sum_div, field]
    _ ≤ r * ((card G * Y) / card G) := by gcongr
    _ = r * Y := by field

/-- The left kernel of a singular matrix over a field with `q` elements has at least `q`
elements. -/
lemma card_le_card_filter_vecMul_eq_zero [DecidableEq m] [Fintype k] [DecidableEq k]
    {Z : Matrix m m k} (hZ : Z.det = 0) : Fintype.card k ≤ #{y : m → k | y ᵥ* Z = 0} := by
  -- The kernel holds the `q` multiples of some `y ≠ 0`.
  obtain ⟨y, hy, hyZ⟩ : ∃ y : m → k, y ≠ 0 ∧ y ᵥ* Z = 0 := exists_vecMul_eq_zero_iff.2 hZ
  exact card_le_card_of_injOn (fun t : k ↦ t • y) (by simp [smul_vecMul, hyZ])
    (smul_left_injective k hy).injOn

/-- Let `π` be a representation of a finite group `G` by `n × n` matrices over a field with `q`
elements, and let `π' s` be the inverse transpose of `π s`. Let `A₀` and `A₁` be two `n × m`
matrices, and let `Θ ≥ 0` be of positive type: `Θ (a⁻¹ * b) = ⟪u a, u b⟫`. Suppose that, for every
`v ≠ 0`, each of two sums of `Θ` is at most `Y ≥ 0`: the sum over the `s` with `π s` fixing `A₀ v`,
and the sum over the `s` with `π' s` fixing `A₁ v`. Then `q · Θ {s | det (A₁ᵀ π(s) A₀) = 0} ≤ 2
Θ(G) + q ^ (|m| + |n| / 2) Y`. -/
lemma card_mul_sum_det_eq_zero_le [DecidableEq m] [Fintype k] [DecidableEq k] (π : G →* GL n k)
    (A₀ A₁ : Matrix n m k) {Θ : G → ℝ} (hΘ : ∀ s : G, 0 ≤ Θ s)
    (hu : ∀ a b : G, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) (Y : ℝ) (hY : 0 ≤ Y)
    (h_fix₀ : ∀ v : m → k, v ≠ 0 → ∑ s : G with A₀ *ᵥ v = π s • A₀ *ᵥ v, Θ s ≤ Y)
    (h_fix₁ : ∀ v : m → k, v ≠ 0 →
      ∑ s : G with A₁ *ᵥ v = invTransposeGL (π s) • A₁ *ᵥ v, Θ s ≤ Y) :
    Fintype.card k * ∑ s : G with (A₁ᵀ * (π s).val * A₀).det = 0, Θ s ≤
      2 * ∑ s : G, Θ s +
        Fintype.card k ^ Fintype.card m * √(Fintype.card k ^ Fintype.card n) * Y := by
  -- With `ψ` a primitive additive character, `∑ y, 𝔼 v, ψ (yᵀ Z v)` counts the left kernel of
  -- `Z = A₁ᵀ π(s) A₀`, which has at least `q` elements if `det Z = 0`. Sum against `Θ` over `s`
  -- first: the terms with `y = 0` or `v = 0` give `Θ(G)`, the others are at most `q^(|n|/2) Y`.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ.IsPrimitive :=
    ⟨_, FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  set r : ℝ := √((card k : ℝ) ^ card n)
  let Z (s : G) : Matrix m m k := A₁ᵀ * (π s).val * A₀
  let W (y v : m → k) (s : G) : ℂ := ψ (y ᵥ* Z s ⬝ᵥ v) * Θ s
  -- On either axis the character is one. Elsewhere both stabiliser bounds apply.
  have term_le (y v : m → k) : (∑ s, W y v s).re ≤
      (if y = 0 then ∑ s, Θ s else 0) + (if v = 0 then ∑ s, Θ s else 0) + r * Y := by
    by_cases h : y = 0 ∨ v = 0
    · have h_rY : 0 ≤ r * Y := by positivity
      have h_total : 0 ≤ ∑ s, Θ s := sum_nonneg fun s _ ↦ hΘ s
      obtain rfl | rfl := h <;> simp [W] <;> split_ifs <;> linarith
    · rw [not_or] at h
      have h_dot (s : G) : y ᵥ* Z s ⬝ᵥ v = (A₁ *ᵥ y) ⬝ᵥ (π s • A₀ *ᵥ v) := by
        simp [Z, Units.smul_def, dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
      simpa [W, h.1, h.2, h_dot] using
        re_sum_addChar_dotProduct_mul_le hψ π hu (h_fix₁ y h.1) (h_fix₀ v h.2)
  -- By orthogonality of characters, the mean over `v` is the mass of the `s` with `y` in the left
  -- kernel of `Z s`.
  have mean_eq (y : m → k) : 𝔼 v : m → k, (∑ s, W y v s).re = ∑ s with y ᵥ* Z s = 0, Θ s := by
    rw [← re_expect, expect_sum_comm]
    simp [W, ← expect_mul, Fintype.expect_eq_sum_div_card, sum_addChar_dotProduct hψ,
      ite_div, sum_filter, apply_ite Complex.re]
  calc card k * ∑ s with (Z s).det = 0, Θ s
      ≤ ∑ s, #{y | y ᵥ* Z s = 0} * Θ s := by
        rw [mul_sum, sum_filter]
        gcongr with s
        split_ifs with hs
        · exact mul_le_mul_of_nonneg_right (mod_cast card_le_card_filter_vecMul_eq_zero hs) (hΘ s)
        · exact mul_nonneg (Nat.cast_nonneg _) (hΘ s)
    _ = ∑ y : m → k, ∑ s with y ᵥ* Z s = 0, Θ s := by
      simp only [sum_filter, natCast_card_filter, sum_mul, boole_mul]
      exact sum_comm
    _ = ∑ y : m → k, 𝔼 v : m → k, (∑ s, W y v s).re := by simp only [mean_eq]
    _ ≤ ∑ y : m → k, 𝔼 v : m → k,
        ((if y = 0 then ∑ s, Θ s else 0) + (if v = 0 then ∑ s, Θ s else 0) + r * Y) :=
      sum_le_sum fun y _ ↦ expect_le_expect fun v _ ↦ term_le y v
    _ = 2 * ∑ s, Θ s + card k ^ card m * r * Y := by
      -- Each axis gives `Θ(G)`: one `y` in the sum, and `q ^ |m|` times a mean `Θ(G) / q ^ |m|`.
      simp [expect_add_distrib, NNRat.smul_def, field, two_mul, sum_add_distrib]

end New
