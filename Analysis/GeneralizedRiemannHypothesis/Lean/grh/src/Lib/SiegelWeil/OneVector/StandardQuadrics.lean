import Lib.DiscreteSeries.Bruhat.QuadricBlocks
import Lib.SiegelWeil.OneVector.SemilocalDensityBounds

/-!
# The quadrics of the standard form at a finite place

At a finite place the standard hermitian form of rank at least two has a basis that begins with a
hyperbolic pair. So the volume disintegrates along the form, and the local density bound applies to
the measures of its quadrics.

* `New.Floors.IntegralPlace.isDisintegration_of_hyperbolic_basis`: the disintegration.
* `New.Floors.IntegralPlace.exists_kernel_isDisintegration_le`: if ψ is trivial on traces,
  ζ_R(μ) ≤ 2 and the rank is at least 2μ + 2, then some s-finite kernel is a disintegration of the
  volume for which the points y of a quadric with u y integral, for a unit u, have bounded mass.

Notions from other files:
* `New.Floors.Place.IsDisintegration`: a family of measures on the quadrics of a form, continuous
  in the index, whose integral over the index is a given measure.
* `New.Floors.Place.quadricMeasure`: the measure on a quadric of a hyperbolic plane plus a form.
* `New.idealZeta`: the sum ζ_R(s) of [R : I]^(−s) over the ideals I of finite index in R.
* `New.Floors.coordinateBox`: the vectors with all coordinates in a given set.

## Relation to the literature

Known result: a local density bound for hermitian forms. See
`Lib.SiegelWeil.OneVector.SiegelClassSum`.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ProbabilityTheory ENNReal Fintype FloorGroups Place SemilocalField
  Function

section Place

variable {A ι κ : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [P : Place A] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Let `B` have as many columns as rows, with Gram matrix `planeSumGram S` for the form `T`: a
hyperbolic plane plus `S`. Let `det T` have modulus one (a matrix scales the volume by the modulus
of its determinant) and let `S` be hermitian with `S * S = 1`, so that the columns of `B` are a
basis. Then `B` carries the measures `P.quadricMeasure S b`, on the quadrics of norm `δ⁻¹ b` for
`planeSumGram S` (`δ = P.skewUnit`), to a disintegration of the volume along `T`: they are the fiber
measures of the volume on the quadrics `x* T x = δ⁻¹ b`. -/
lemma Place.isDisintegration_map_quadricMeasure {T : Matrix ι ι A}
    {S : Matrix κ κ A} {B : Matrix ι (Fin 2 ⊕ κ) A} (h_gram : Bᴴ * T * B = planeSumGram S)
    (h_card : card ι = card (Fin 2 ⊕ κ)) (hT : P.modulus T.det = 1) (hS : Sᴴ = S)
    (hS_sq : S * S = 1) :
    P.IsDisintegration volume T
      fun b : skewAdjoint A ↦ (P.quadricMeasure S b).map (B *ᵥ ·) := by
  have h_plane : planeSumGram S * planeSumGram S = 1 := by
    simp [fromBlocks_multiply, hS_sq, ← one_fin_two]
  -- Reindex the columns of `B` to get a square matrix `M`. Its Gram matrix has square one.
  let e : ι ≃ Fin 2 ⊕ κ := equivOfCardEq h_card
  let M : Matrix ι ι A := B * inclMatrix A e
  have gram_sq : (Mᴴ * T * M) ^ 2 = 1 := by
    rw [gram_mul, h_gram, gram_inclMatrix, sq, submatrix_mul_equiv, h_plane, submatrix_one_equiv]
  have h_unit : IsUnit M.det := by
    rw [sq, ← mul_assoc] at gram_sq
    exact isUnit_det_of_left_inverse gram_sq
  -- Taking determinants, `modulus M.det ^ 4 = 1`; so `B` keeps the volume.
  have h_mod : P.modulus M.det = 1 := by
    have h_star : P.modulus (star M.det) = P.modulus M.det := (P.modulus_star_and_neg M.det).left
    have h_pow : P.modulus M.det ^ 4 = 1 :=
      calc
        P.modulus M.det ^ 4 = (P.modulus (star M.det) * P.modulus T.det * P.modulus M.det) ^ 2 := by
          rw [h_star, hT]
          ring
        _ = P.modulus ((Mᴴ * T * M) ^ 2).det := by
          simp only [det_pow, det_mul, det_conjTranspose, map_pow, map_mul]
        _ = 1 := by rw [gram_sq, det_one, map_one]
    exact (ENNReal.pow_right_strictMono four_ne_zero).injective (h_pow.trans (one_pow 4).symm)
  have h_vol : volume.map (B *ᵥ ·) = volume :=
    calc
      volume.map (B *ᵥ ·) = (volume.map (inclMatrix A e *ᵥ ·)).map (B *ᵥ ·) := by
        rw [(measurePreserving_inclMatrix e).map_eq]
      _ = volume.map (M *ᵥ ·) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        simp only [M, comp_def, mulVec_mulVec]
      _ = volume := by rw [P.map_mulVec_volume ι M h_unit, h_mod, inv_one, one_smul]
  have h_left : planeSumGram S * (Bᴴ * T) * B = 1 := by
    rw [Matrix.mul_assoc, h_gram, h_plane]
  rw [← h_vol]
  exact (isDisintegration_quadricMeasure hS).map h_gram h_left

end Place

variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype κ]

/-- A finite type with at least two elements has the cardinality of a pair plus a rest. -/
lemma card_eq_card_pair_sum (h : 2 ≤ card κ) : card κ = card (Fin 2 ⊕ Fin (card κ - 2)) := by
  rw [card_sum, card_fin, card_fin, Nat.add_sub_cancel' h]

/-- At a finite place, the standard hermitian form of rank at least two has a basis that begins
with a hyperbolic pair and ends with orthonormal vectors: its Gram matrix is `planeSumGram 1`. -/
lemma IntegralPlace.exists_hyperbolic_basis (h : 2 ≤ card κ) :
    ∃ B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A, Bᴴ * B = planeSumGram 1 := by
  -- With `c̄ c = -1` and `τ + τ̄ = 1`, two orthonormal vectors `x`, `y` give the hyperbolic pair
  -- `x + c y`, `τ̄ x - τ c y`.
  obtain ⟨c, -, hc⟩ : ∃ c : A, c ∈ P.integers ∧ star c * c = -1 := P.isAdelic.exists_norm_neg_one
  have hτ : P.element + star P.element = 1 := P.element_add_star
  let e : κ ≃ Fin 2 ⊕ Fin (card κ - 2) := equivOfCardEq (card_eq_card_pair_sum h)
  let C : Matrix (Fin 2) (Fin 2) A := !![1, star P.element; c, -(P.element * c)]
  have hC : Cᴴ * C = !![0, 1; 1, 0] :=
    calc
      Cᴴ * C = !![1 + star c * c, star P.element - P.element * (star c * c);
          P.element - star P.element * (star c * c),
            P.element * star P.element + P.element * star P.element * (star c * c)] := by
        simp [C, ← ext_iff, mul_apply, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      _ = !![0, 1; 1, 0] := by simp [hc, hτ, add_comm (star P.element)]
  -- The basis is `C` on the first two vectors and the identity on the rest.
  let D : Matrix (Fin 2 ⊕ Fin (card κ - 2)) (Fin 2 ⊕ Fin (card κ - 2)) A := fromBlocks C 0 0 1
  have hD : Dᴴ * D = planeSumGram 1 := by
    simp [D, fromBlocks_conjTranspose, fromBlocks_multiply, hC]
  refine ⟨D.submatrix e id, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hD, submatrix_id_id]

variable [DecidableEq κ]

/-- Let `A` be a finite place and let `κ` have at least two elements. Let `B` be a basis for the
standard form on `κ → A` with Gram matrix `planeSumGram 1`: a hyperbolic pair, then orthonormal
vectors. It carries the measures `P.quadricMeasure 1 b`, for skew `b`, on the quadrics of norm
`δ⁻¹ b` for `planeSumGram 1` (`δ = P.skewUnit`), to a disintegration of the volume along
`x ↦ x* x`: they are its fiber measures on the quadrics `x* x = δ⁻¹ b`. -/
lemma IntegralPlace.isDisintegration_of_hyperbolic_basis (h_rank : 2 ≤ card κ)
    {B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A} (hB : Bᴴ * B = planeSumGram 1) :
    P.IsDisintegration volume (1 : Matrix κ κ A)
      fun b : skewAdjoint A ↦ (P.quadricMeasure 1 b).map (B *ᵥ ·) :=
  have h_gram : Bᴴ * (1 : Matrix κ κ A) * B = planeSumGram 1 := by rw [Matrix.mul_one, hB]
  have h_det : P.modulus (1 : Matrix κ κ A).det = 1 := by simp
  isDisintegration_map_quadricMeasure h_gram (card_eq_card_pair_sum h_rank) h_det
    conjTranspose_one (mul_one 1)

/-- Let A be a finite place whose additive character ψ is trivial on traces x + x̄, let ζ_R(μ) ≤ 2,
and let κ have r + 1 ≥ 2μ + 2 elements. Then the volume of A^κ disintegrates along the standard
form x ↦ x* x into an s-finite kernel l, with l β on the quadric x* x = δ⁻¹ β for skew β, and for a
unit u the set `coordinateBox` of the points y with all u y_i in R has mass at most ζ_R(μ) |u|^(-r)
for each l β. Here R is the ring of integers of A, δ = `skewUnit`, ζ_R(μ) = `idealZeta R μ` is the
sum of [R : I]^(-μ) over the ideals I of finite index, and |x| = `modulus x` is the factor by which
multiplication by x scales the volume of A. -/
theorem IntegralPlace.exists_kernel_isDisintegration_le {μ r : ℕ}
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) (hμ : idealZeta P.integers μ ≤ 2) (h_card : card κ = r + 1)
    (h_rank : 2 * μ + 1 ≤ r) :
    ∃ l : Kernel (skewAdjoint A) (κ → A), IsSFiniteKernel l ∧
      P.IsDisintegration volume (1 : Matrix κ κ A) l ∧
      ∀ (β : skewAdjoint A) (u : Aˣ), l β (coordinateBox κ {x : A | u.val * x ∈ P.integers}) ≤
        idealZeta P.integers μ * (P.modulus u)⁻¹ ^ r := by
  have h_two : 2 ≤ card κ := by lia
  obtain ⟨B, hB⟩ : ∃ B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A, Bᴴ * B = planeSumGram 1 :=
    P.exists_hyperbolic_basis h_two
  -- The kernel is the image of the measure of the parameters under the flat chart, followed by B.
  obtain ⟨l, h_sfinite, hl⟩ := exists_kernel_eq_map (volume.prod P.skewMeasure)
    (K := fun q : skewAdjoint A × (A × (Fin (card κ - 2) → A)) × skewAdjoint A ↦
      B *ᵥ flatChart 1 q.1 q.2) (by fun_prop)
  have h_dis : P.IsDisintegration volume (1 : Matrix κ κ A) l := by
    have h_eq : (l : skewAdjoint A → Measure (κ → A)) =
        fun b : skewAdjoint A ↦ (P.quadricMeasure 1 b).map (B *ᵥ ·) := by
      ext1 b
      rw [hl, Measure.map_map (by fun_prop) (by fun_prop), comp_def]
    rw [h_eq]
    exact P.isDisintegration_of_hyperbolic_basis h_two hB
  refine ⟨l, h_sfinite, h_dis, fun β u ↦ ?_⟩
  -- These points are the class of 0 modulo u⁻¹, of volume |u|^(-(r+1)).
  have h_class : coordinateBox κ {x : A | u.val * x ∈ P.integers} = residueClass u⁻¹ 0 := by
    simp [Set.ext_iff, residueClass, mem_latticeMultiple]
  have h_one : IsUnimodular P.integers (1 : Matrix κ κ A) :=
    ⟨conjTranspose_one, 1, one_mem _, Units.val_one⟩
  have h_cancel : P.modulus u * (P.modulus u)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  calc
    l β (coordinateBox κ {x : A | u.val * x ∈ P.integers}) = l β (residueClass u⁻¹ 0) := by
      rw [h_class]
    _ ≤ idealZeta P.integers μ * (P.modulus ↑u⁻¹)⁻¹ * volume (residueClass u⁻¹ (0 : κ → A)) :=
      measure_residueClass_le_idealZeta h_dis h_one hψ hμ (by lia) u⁻¹ 0 β
    _ = idealZeta P.integers μ * (P.modulus u * (P.modulus u)⁻¹) * (P.modulus u)⁻¹ ^ r := by
      rw [volume_residueClass, h_card, modulus_inv, inv_inv, pow_succ']
      ring
    _ = idealZeta P.integers μ * (P.modulus u)⁻¹ ^ r := by rw [h_cancel, mul_one]

end New.Floors
