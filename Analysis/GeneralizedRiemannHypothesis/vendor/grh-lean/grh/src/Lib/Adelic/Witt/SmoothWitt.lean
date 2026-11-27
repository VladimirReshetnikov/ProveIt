import Lib.Adelic.Witt.WittTheorem
import Lib.General.Analysis.MeanValueAndTaylor
import Lib.General.LinearAlgebra.HermitianMatrices

/-!
# Smooth families of isometries that carry an isotropic vector to its neighbours

Let `x₀` and `y₀` be isotropic vectors of a hermitian space over `ℂ` that are not orthogonal.
Elements of the unitary group that depend smoothly on `x` carry `y₀` to `x` for isotropic `x` near
`x₀` (they are built as quasi-reflections). For a form given by signs, each such element, composed
with the inverse of the one at `x₀`, carries `x₀` itself to `x`.

The notions used in the statements:
* `U J` is the unitary group of a matrix `J`: the invertible `g` with `gᴴ * J * g = J`.
* `signMatrix ε` is the diagonal matrix of the signs `ε i`, and `USign ε = U (signMatrix ε)`.

## Relation to the literature

Known result: Witt's extension theorem for hermitian forms, here in a smooth local form for
isotropic vectors. See also `Lib.Adelic.Witt.IwasawaDecomposition`.
-/

namespace New.Exchange

open Matrix ContDiff Norms.Elementwise Filter

variable {m : Type} [Fintype m] [DecidableEq m]

/-- For every neighbourhood `N` of `x₀` in a finite-dimensional real normed space there is a
smooth map of the whole space into `N` that is the identity near `x₀`. -/
lemma exists_contDiff_mem_eventually_eq_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {x₀ : X} {N : Set X} (hN : N ∈ nhds x₀) :
    ∃ ρ : X → X, ContDiff ℝ ∞ ρ ∧ (∀ x : X, ρ x ∈ N) ∧ ∀ᶠ x : X in nhds x₀, ρ x = x := by
  obtain ⟨r, hr, h_ball⟩ := Metric.mem_nhds_iff.1 hN
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨fun x ↦ x₀ + b x • (x - x₀), ?_, fun x ↦ h_ball ?_, ?_⟩
  · exact contDiff_const.add (b.contDiff.smul (contDiff_id.sub contDiff_const))
  · rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg b.nonneg]
    rcases lt_or_ge ‖x - x₀‖ r with h_near | h_far
    · exact (mul_le_of_le_one_left (norm_nonneg _) b.le_one).trans_lt h_near
    · rwa [b.zero_of_le_dist (h_far.trans_eq (dist_eq_norm x x₀).symm), zero_mul]
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]

/-- Let `J` be an invertible hermitian matrix, and let `x₀` and `y₀` be isotropic and not
orthogonal for the form `(v, w) ↦ star v ⬝ᵥ J *ᵥ w`. There are elements `k x` of the unitary
group `U J` of this form, smooth in `x`, with `k x *ᵥ y₀ = x` for all isotropic `x` near `x₀`. -/
lemma exists_contDiff_carrying_isotropic {J : Matrix m m ℂ} (hJ : Jᴴ = J) (hJ_unit : IsUnit J)
    {x₀ y₀ : m → ℂ} (hx₀ : star x₀ ⬝ᵥ J *ᵥ x₀ = 0) (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0)
    (h_pair : star x₀ ⬝ᵥ J *ᵥ y₀ ≠ 0) :
    ∃ k : (m → ℂ) → U J, ContDiff ℝ ∞ (fun x : m → ℂ ↦ (k x : Matrix m m ℂ)) ∧
      ∀ᶠ x : m → ℂ in nhds x₀, star x ⬝ᵥ J *ᵥ x = 0 → (k x : Matrix m m ℂ) *ᵥ y₀ = x := by
  -- The quasi-reflection along `y₀ - x` with denominator `σ x` is defined where `σ x ≠ 0`;
  -- compose it with a smooth map into that set that is the identity near `x₀`.
  let σ (x : m → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x / 2 - star x ⬝ᵥ J *ᵥ y₀
  have hσ_smooth : ContDiff ℝ ∞ σ := by
    simp only [σ, dotProduct, mulVec, Pi.star_apply, RCLike.star_def]
    fun_prop
  have hσ_trace (x : m → ℂ) : σ x + star (σ x) = star (y₀ - x) ⬝ᵥ J *ᵥ (y₀ - x) := by
    simp only [σ, star_sub, star_div₀, star_dotProduct_mulVec_comm hJ, star_ofNat, mulVec_sub,
      sub_dotProduct,
      dotProduct_sub, hy₀]
    ring
  have hσ_ne : ∀ᶠ x in nhds x₀, σ x ≠ 0 :=
    hσ_smooth.continuous.continuousAt.eventually_ne (by simpa [σ, hx₀] using h_pair)
  obtain ⟨ρ, hρ_smooth, hρ_ne, hρ_eq⟩ := exists_contDiff_mem_eventually_eq_self hσ_ne
  refine ⟨fun x ↦ quasiReflection hJ hJ_unit (y₀ - ρ x) (.mk0 (σ (ρ x)) (hρ_ne x))
    (hσ_trace (ρ x)), ?_, ?_⟩
  · have h_inv : ContDiff ℝ ∞ fun x ↦ (σ (ρ x))⁻¹ := (hσ_smooth.comp hρ_smooth).inv hρ_ne
    refine contDiff_pi' fun i ↦ contDiff_pi' fun j ↦ ?_
    suffices h_entry : ContDiff ℝ ∞ fun x ↦ (1 : Matrix m m ℂ) i j - (σ (ρ x))⁻¹ *
        ((y₀ i - ρ x i) * ∑ l, starRingEnd ℂ (y₀ l - ρ x l) * J l j) by
      simpa [quasiReflection, vecMulVec_apply, vecMul, dotProduct] using h_entry
    fun_prop
  · filter_upwards [hρ_eq, hσ_ne] with x hx h_ne h_iso
    have h_form : star (y₀ - x) ⬝ᵥ J *ᵥ y₀ = σ x := by simp [σ, hy₀, h_iso]
    -- the quasi-reflection subtracts from `y₀` the vector `y₀ - x`, with coefficient `1`;
    -- `-star_sub` keeps the form in the shape of `h_form`
    suffices h_reflect : y₀ - ((σ x)⁻¹ * (star (y₀ - x) ⬝ᵥ J *ᵥ y₀)) • (y₀ - x) = x by
      simpa [quasiReflection, hx, sub_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
        smul_smul, -star_sub] using h_reflect
    rw [h_form, inv_mul_cancel₀ h_ne, one_smul, sub_sub_cancel]

/-- Let `x₀ ≠ 0` be isotropic for the form of `signMatrix ε`, the diagonal matrix of the signs `ε`.
There are elements `k x` of its unitary group `USign ε`, smooth in `x`, that carry `x₀` to `x` for
all isotropic `x` near `x₀`. -/
lemma exists_contDiff_eventually_mulVec_eq {ε : m → ℤˣ} {x₀ : m → ℂ} (h_ne : x₀ ≠ 0)
    (h_iso : star x₀ ⬝ᵥ signMatrix ε *ᵥ x₀ = 0) :
    ∃ k : (m → ℂ) → USign ε, ContDiff ℝ ∞ (fun x : m → ℂ ↦ (k x : Matrix m m ℂ)) ∧
      ∀ᶠ x : m → ℂ in nhds x₀,
        star x ⬝ᵥ signMatrix ε *ᵥ x = 0 → (k x : Matrix m m ℂ) *ᵥ x₀ = x := by
  -- Pass from `x₀` to `J x₀`, which is isotropic and not orthogonal to `x₀`, and from there to `x`.
  let J : Matrix m m ℂ := signMatrix ε
  have hJ : Jᴴ = J := IsHermitianInvolution.isHermitian
  have hJJ : J *ᵥ J *ᵥ x₀ = x₀ := by rw [mulVec_mulVec, IsHermitianInvolution.mul_self, one_mulVec]
  have hy_iso : star (J *ᵥ x₀) ⬝ᵥ J *ᵥ J *ᵥ x₀ = 0 := by
    rwa [hJJ, star_mulVec, hJ, ← dotProduct_mulVec]
  have h_pair : star x₀ ⬝ᵥ J *ᵥ J *ᵥ x₀ ≠ 0 := by
    open ComplexOrder in rwa [hJJ, Ne, dotProduct_star_self_eq_zero]
  obtain ⟨r, hr_smooth, hr⟩ : ∃ r : (m → ℂ) → U J, ContDiff ℝ ∞ (fun x ↦ (r x : Matrix m m ℂ)) ∧
      ∀ᶠ x in nhds x₀, star x ⬝ᵥ J *ᵥ x = 0 → (r x : Matrix m m ℂ) *ᵥ J *ᵥ x₀ = x :=
    exists_contDiff_carrying_isotropic hJ IsHermitianInvolution.isUnit h_iso hy_iso h_pair
  have hr₀ : (↑(r x₀)⁻¹ : Matrix m m ℂ) *ᵥ x₀ = J *ᵥ x₀ :=
    calc _ = (↑(r x₀)⁻¹ : Matrix m m ℂ) *ᵥ (r x₀ : Matrix m m ℂ) *ᵥ J *ᵥ x₀ := by
          rw [hr.self_of_nhds h_iso]
      _ = J *ᵥ x₀ := by rw [mulVec_mulVec, Subgroup.coe_inv, Units.inv_mul, one_mulVec]
  refine ⟨fun x ↦ r x * (r x₀)⁻¹, contDiff_matrix_mul.comp (hr_smooth.prodMk contDiff_const), ?_⟩
  filter_upwards [hr] with x h_carry hx
  rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hr₀, h_carry hx]

end New.Exchange
