import OAI.Combinatorics.Progressions.Estimates.AdaptedTranslation
import OAI.Combinatorics.Progressions.Estimates.LowerStepSquare
import OAI.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def normalizedShiftLog (s : ℕ) (h : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) : VectorPolynomial σ ℚ L :=
  lieBCH s (monomial 0 a) (lieBCH s (translate h p) (monomial 0 b))

theorem eval_normalizedShiftLog (s : ℕ) (h x : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) :
    eval x (normalizedShiftLog s h a b p) = lieBCH s a (lieBCH s (eval (fun i => x i + h i) p) b) := by
  simp only [normalizedShiftLog, eval_lieBCH, eval_translate, eval_monomial,
    Finsupp.prod_zero_index, one_smul]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem normalizedShiftLog_adapted (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted w (normalizedShiftLog s h a b p) :=
  F.adapted_bch w (F.adapted_constant w a)
    (F.adapted_bch w (F.adapted_translate w hw h hp) (F.adapted_constant w b))

theorem normalizedShiftLog_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (normalizedShiftLog s h a b p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  let p₀ : F.adaptedLieSubalgebra w := ⟨p, (F.mem_adaptedSubmodule w p).mpr hp⟩
  let p₁ : F.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h hp)⟩
  let c₁ := F.adaptedConstant w a
  let c₂ := F.adaptedConstant w b
  let I := F.shiftedAdaptedIdeal w
  let z := lieBCH s c₁ (lieBCH s p₁ c₂)
  have hz₁ : z - lieBCH s p₁ c₂ ∈ I :=
    lieBCH_sub_right_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I
      (F.adaptedConstant_mem_shiftedIdeal w a) _
  have hz₂ : lieBCH s p₁ c₂ - p₁ ∈ I :=
    lieBCH_sub_left_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I _
      (F.adaptedConstant_mem_shiftedIdeal w b)
  have hz₃ : p₁ - p₀ ∈ I := F.translate_sub_coefficient_mem w hw h hp
  have hz : z - p₀ ∈ I := by
    have hh := I.add_mem (I.add_mem hz₁ hz₂) hz₃
    have he : (z - lieBCH s p₁ c₂ + (lieBCH s p₁ c₂ - p₁)) + (p₁ - p₀) = z - p₀ := by abel
    rw [he] at hh
    exact hh
  have he : (F.adaptedLieSubalgebra w).incl z = normalizedShiftLog s h a b p := by
    dsimp only [z]
    rw [map_lieBCH, map_lieBCH]
    rfl
  have hh := hz α
  change coefficients ((F.adaptedLieSubalgebra w).incl (z - p₀)) α ∈ _ at hh
  rw [map_sub, he] at hh
  exact hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem positive_weight_of_ne_zero (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) : 0 < Finsupp.weight w α := by
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hα
  exact (hw i).trans_le (Finsupp.le_weight_of_ne_zero' w hi)

theorem exists_square_polynomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) (hq : F.Adapted w q)
    (hdiff : ∀ α, coefficients (p - q) α ∈ F.layer (Finsupp.weight w α + 1))
    (hzero : coefficients (p - q) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = q := by
  simp only [map_sub, Finsupp.sub_apply] at hdiff hzero
  have hcoeff (α : σ →₀ ℕ) : coefficients (pair p q) α ∈ F.squareLieSubalgebra.toSubmodule := by
    rw [coefficients_pair]
    change (coefficients p α, coefficients q α) ∈ F.squareLieSubalgebra
    rw [F.mem_squareLieSubalgebra]
    change coefficients p α - coefficients q α ∈ F.layer 2
    by_cases hα : α = 0
    · simpa only [hα] using hzero
    · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (hdiff α)
  let r := restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p q) hcoeff
  have hr (α : σ →₀ ℕ) : (coefficients r α : L × L) = (coefficients p α, coefficients q α) := by
    rw [coefficients_restrictCoefficients, coefficients_pair]
  refine ⟨r, ?_, ?_, ?_⟩
  · apply (F.squareFiltration.adapted_iff_coefficients w r).mpr
    intro α
    rw [F.mem_squareFiltration_layer, hr, F.mem_squareLayer]
    exact ⟨(F.adapted_iff_coefficients w p).mp hp α,
      (F.adapted_iff_coefficients w q).mp hq α, hdiff α⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.1 = coefficients p α
    rw [hr]
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.2 = coefficients q α
    rw [hr]

theorem exists_normalized_shift_square (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p)
    (hzero : coefficients (normalizedShiftLog s h a b p - p) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = normalizedShiftLog s h a b p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = p :=
  F.exists_square_polynomial w hw _ _ (F.normalizedShiftLog_adapted w hw h a b hp) hp
    (F.normalizedShiftLog_sub_coefficient_mem w hw h a b hp) hzero

theorem square_polynomial_quotient_adapted (F : NilpotentLieFiltration L (s + 1))
    (w : σ → ℕ) {r : VectorPolynomial σ ℚ F.squareLieSubalgebra}
    (hr : F.squareFiltration.Adapted w r) :
    F.squareFiltration.quotientTop.Adapted w
      (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap r) :=
  F.squareFiltration.adapted_quotientLie _ le_rfl w hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

abbrev PolynomialSymbol (w : σ → ℕ) :=
  F.adaptedLieSubalgebra w ⧸ F.shiftedAdaptedIdeal w

noncomputable def polynomialSymbolMap (w : σ → ℕ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  lieQuotientMap (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_surjective (w : σ → ℕ) :
    Function.Surjective (F.polynomialSymbolMap w) :=
  lieQuotientMap_surjective (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_eq_zero_iff (w : σ → ℕ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 1) :=
  lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) p

theorem polynomialSymbolMap_eq_iff (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = F.polynomialSymbolMap w q ↔
      ∀ α, coefficients ((p : VectorPolynomial σ ℚ L) - (q : VectorPolynomial σ ℚ L)) α ∈
        F.layer (Finsupp.weight w α + 1) := by
  rw [← sub_eq_zero, ← map_sub, F.polynomialSymbolMap_eq_zero_iff]
  rfl

theorem polynomialSymbolMap_lieBCH (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w (lieBCH s p q) =
      lieBCH s (F.polynomialSymbolMap w p) (F.polynomialSymbolMap w q) :=
  map_lieBCH (F.polynomialSymbolMap w) s p q

theorem polynomialSymbol_lowerCentralSeries_eq_bot (w : σ → ℕ) :
    LieModule.lowerCentralSeries ℚ (F.PolynomialSymbol w) (F.PolynomialSymbol w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.shiftedAdaptedIdeal w)

abbrev PolynomialSymbolGroup (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.PolynomialSymbol w) s (F.polynomialSymbol_lowerCentralSeries_eq_bot w)

noncomputable def polynomialSymbolHom (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.polynomialSymbolMap w)

@[simp] theorem polynomialSymbolHom_coord (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialSymbolHom w g).coord = F.polynomialSymbolMap w g.coord := rfl

theorem polynomialSymbolHom_surjective (w : σ → ℕ) :
    Function.Surjective (F.polynomialSymbolHom w) := by
  intro g
  obtain ⟨p, hp⟩ := F.polynomialSymbolMap_surjective w g.coord
  exact ⟨⟨p⟩, NilpotentLieBCHGroup.ext hp⟩

@[simp] theorem polynomialSymbolMap_constant (w : σ → ℕ) (a : L) :
    F.polynomialSymbolMap w (F.adaptedConstant w a) = 0 :=
  (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
    (F.adaptedConstant_mem_shiftedIdeal w a)

theorem polynomialSymbolMap_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w
      ⟨translate h (p : VectorPolynomial σ ℚ L),
        (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h
          ((F.mem_adaptedSubmodule w _).mp p.property))⟩ =
      F.polynomialSymbolMap w p := by
  apply (F.polynomialSymbolMap_eq_iff w _ p).mpr
  exact F.translate_sub_coefficient_mem w hw h ((F.mem_adaptedSubmodule w _).mp p.property)

theorem polynomialSymbolMap_normalizedShift (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w
      ⟨normalizedShiftLog s h a b (p : VectorPolynomial σ ℚ L),
        (F.mem_adaptedSubmodule w _).mpr (F.normalizedShiftLog_adapted w hw h a b
          ((F.mem_adaptedSubmodule w _).mp p.property))⟩ =
      F.polynomialSymbolMap w p := by
  apply (F.polynomialSymbolMap_eq_iff w _ p).mpr
  exact F.normalizedShiftLog_sub_coefficient_mem w hw h a b
    ((F.mem_adaptedSubmodule w _).mp p.property)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem exponent_of_weight_le_one {σ : Type*} (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1) :
    α = 0 ∨ ∃ i, α = Finsupp.single i 1 := by
  by_cases hz : α = 0
  · exact Or.inl hz
  · right
    have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hz
    have he : Finsupp.weight (fun _ : σ => 1) α = 1 := by omega
    apply (Finsupp.sum_eq_one_iff α).mp
    simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one] using he

theorem eq_affine_of_degreeLE_one {σ R V : Type*} [Fintype σ]
    [CommRing R] [AddCommGroup V] [Module R V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) :
    p = monomial 0 (coefficients p 0) +
      linearPolynomial (fun i => coefficients p (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  ext α
  rw [map_add, Finsupp.add_apply, coefficients_monomial]
  by_cases hz : α = 0
  · subst α
    rw [Finsupp.single_eq_same, coefficients_linearPolynomial_zero, add_zero]
  · rw [Finsupp.single_eq_of_ne hz, zero_add]
    by_cases hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1
    · obtain hzero | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα
      · exact (hz hzero).elim
      · rw [coefficients_linearPolynomial_single]
    · rw [hp α (Nat.lt_of_not_ge hα)]
      symm
      apply coefficients_linearPolynomial_of_ne
      intro i hi
      apply hα
      rw [← hi]
      simp only [Finsupp.weight_single, one_smul, le_refl]

theorem eval₂_affine_of_degreeLE_one {σ R S V : Type*} [Fintype σ]
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) (t : σ → S) :
    eval₂ t p = coefficients p 0 + ∑ i, t i • coefficients p (Finsupp.single i 1) := by
  conv_lhs => rw [eq_affine_of_degreeLE_one p hp]
  rw [map_add, eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedCoefficientMap (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp
    (coefficients.toLinearMap.comp (F.adaptedLieSubalgebra w).incl.toLinearMap)

@[simp] theorem adaptedCoefficientMap_apply (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.adaptedCoefficientMap w α p = coefficients (p : VectorPolynomial σ ℚ L) α := rfl

noncomputable def polynomialSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] L ⧸ F.layer (Finsupp.weight w α + 1) :=
  (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.layer (Finsupp.weight w α + 1)).mkQ.comp (F.adaptedCoefficientMap w α)) (by
      intro p hp
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hp α))

@[simp] theorem polynomialSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolMap w p) =
      (F.layer (Finsupp.weight w α + 1)).mkQ (coefficients (p : VectorPolynomial σ ℚ L) α) := rfl

theorem polynomialSymbolCoefficient_mem_layer_image (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : F.PolynomialSymbol w) :
    ∃ v ∈ F.layer (Finsupp.weight w α),
      (F.layer (Finsupp.weight w α + 1)).mkQ v = F.polynomialSymbolCoefficient w α x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  exact ⟨coefficients (p : VectorPolynomial σ ℚ L) α, p.property α, rfl⟩

theorem polynomialSymbol_ext (w : σ → ℕ) (x y : F.PolynomialSymbol w)
    (h : ∀ α, F.polynomialSymbolCoefficient w α x = F.polynomialSymbolCoefficient w α y) :
    x = y := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
  apply (F.polynomialSymbolMap_eq_iff w p q).mpr
  intro α
  have he := h α
  rw [F.polynomialSymbolCoefficient_map, F.polynomialSymbolCoefficient_map] at he
  have hzero : (F.layer (Finsupp.weight w α + 1)).mkQ
      (coefficients (p : VectorPolynomial σ ℚ L) α - coefficients (q : VectorPolynomial σ ℚ L) α) = 0 := by
    rw [map_sub, he, sub_self]
  simpa only [map_sub, Finsupp.sub_apply] using (Submodule.Quotient.mk_eq_zero _).mp hzero

theorem polynomialSymbolCoefficient_eq_zero_of_weight_gt (w : σ → ℕ) (α : σ →₀ ℕ)
    (hα : s < Finsupp.weight w α) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolCoefficient w α x = 0 := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolCoefficient_map]
  have hp := F.antitone (Nat.succ_le_of_lt hα) (p.property α)
  have hz : coefficients (p : VectorPolynomial σ ℚ L) α = 0 := by
    simpa only [F.terminal, Submodule.mem_bot] using hp
  rw [hz, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem mem_layer_iff_basis_coordinates (j : ℕ) (v : L) :
    v ∈ F.layer j ↔ ∀ i, ¬ j ≤ ω i → b.repr v i = 0 := by
  rw [hlayers, basis_mem_span_image_iff]
  rfl

theorem adaptedSubmodule_eq_span_tensorBasis (w : σ → ℕ) :
    F.adaptedSubmodule w = Submodule.span ℚ
      (coefficientTensorBasis b '' {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}) := by
  ext p
  change (∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rcases z with ⟨α, i⟩
    rw [coefficientTensorBasis_repr]
    exact h α i hz
  · intro h α i hi
    have hh := h (α, i) hi
    simpa only [coefficientTensorBasis_repr] using hh

noncomputable def adaptedMonomialBasis (w : σ → ℕ) :
    Basis {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} ℚ (F.adaptedLieSubalgebra w) :=
  supportedSubmoduleBasis (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2} (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w)

@[simp] theorem adaptedMonomialBasis_coe (w : σ → ℕ)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w z : VectorPolynomial σ ℚ L) =
      monomial z.val.1 (b z.val.2) := by
  exact (supportedSubmoduleBasis_coe (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) z).trans
      (coefficientTensorBasis_apply b _ _)

theorem adaptedMonomialBasis_repr (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w).repr p z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  exact (supportedSubmoduleBasis_repr (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) p z).trans
      (coefficientTensorBasis_repr b _ _ _)

theorem shiftedAdaptedIdeal_eq_span_monomialBasis (w : σ → ℕ) :
    (F.shiftedAdaptedIdeal w).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hlayers w ''
        {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedWeightedDilation (w : σ → ℕ) (r : ℚ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  { ((weightedDilation w r).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
        rw [coefficients_weightedDilation]
        exact (F.layer _).smul_mem _ (p.property α)) with
    map_lie' := by
      intro p q
      apply Subtype.ext
      exact weightedDilation_lie w r (p : VectorPolynomial σ ℚ L) (q : VectorPolynomial σ ℚ L) }

theorem adaptedWeightedDilation_mem_shiftedIdeal (w : σ → ℕ) (r : ℚ)
    {p : F.adaptedLieSubalgebra w} (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.adaptedWeightedDilation w r p ∈ F.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp α)

noncomputable def polynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((F.polynomialSymbolMap w).toLinearMap.comp (F.adaptedWeightedDilation w r).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
          (F.adaptedWeightedDilation_mem_shiftedIdeal w r hp))
    map_lie' := by
      intro x y
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change F.polynomialSymbolMap w (F.adaptedWeightedDilation w r ⁅p, q⁆) =
        ⁅F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p),
          F.polynomialSymbolMap w (F.adaptedWeightedDilation w r q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem polynomialSymbolDilation_map (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolDilation w r (F.polynomialSymbolMap w p) =
      F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p) := rfl

theorem polynomialSymbolCoefficient_dilation (w : σ → ℕ) (r : ℚ)
    (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolDilation w r x) =
      r ^ Finsupp.weight w α • F.polynomialSymbolCoefficient w α x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolCoefficient_map,
    F.polynomialSymbolCoefficient_map]
  change (F.layer (Finsupp.weight w α + 1)).mkQ
    (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α) = _
  rw [coefficients_weightedDilation, map_smul]

@[simp] theorem polynomialSymbolDilation_one (w : σ → ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w 1 x = x := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, one_pow, one_smul]

theorem polynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w (a * b) x =
      F.polynomialSymbolDilation w a (F.polynomialSymbolDilation w b x) := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, mul_pow, smul_smul]

theorem polynomialSymbolHom_dilation (w : σ → ℕ) (r : ℚ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    F.polynomialSymbolHom w (NilpotentLieBCHGroup.map (F.adaptedWeightedDilation w r) g) =
      NilpotentLieBCHGroup.map (F.polynomialSymbolDilation w r) (F.polynomialSymbolHom w g) := by
  apply NilpotentLieBCHGroup.ext
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedPolynomialFiltration_layer (w : σ → ℕ) (j : ℕ) :
    (F.adaptedPolynomialFiltration w).layer j = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w '' {z | j ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer j) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev SymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 = ω z.2}

def symbolSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    ↥({z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
      Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}ᶜ) ≃ SymbolBasisIndex w ω where
  toFun z := ⟨z.val.val, by
    have hle := z.val.property
    have hlt := z.property
    change ¬ Finsupp.weight w z.val.val.1 + 1 ≤ ω z.val.val.2 at hlt
    omega⟩
  invFun z := ⟨⟨z.val, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2
    have hz := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialSymbolBasis (w : σ → ℕ) :
    Basis (SymbolBasisIndex w ω) ℚ (F.PolynomialSymbol w) :=
  (supportedQuotientBasis (F.adaptedMonomialBasis b ω hlayers w)
    (F.shiftedAdaptedIdeal w).toSubmodule
    {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}
    (F.shiftedAdaptedIdeal_eq_span_monomialBasis b ω hlayers w)).reindex (symbolSurvivorEquiv w ω)

@[simp] theorem polynomialSymbolBasis_apply (w : σ → ℕ) (z : SymbolBasisIndex w ω) :
    F.polynomialSymbolBasis b ω hlayers w z =
      F.polynomialSymbolMap w (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩) := by
  rw [polynomialSymbolBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

theorem polynomialSymbolBasis_repr_map (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [polynomialSymbolBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    ((F.shiftedAdaptedIdeal w).toSubmodule.mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.adaptedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedPolynomialIdeal_eq_span_monomialBasis (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w k).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + k)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

abbrev ShiftedMonomialIndex (w : σ → ℕ) (ω : ι → ℕ) (k : ℕ) :=
  {z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
    Finsupp.weight w z.val.1 + k ≤ ω z.val.2}

noncomputable def shiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℚ (F.shiftedPolynomialIdeal w k) :=
  supportedSubmoduleBasis (F.adaptedMonomialBasis b ω hF w)
    (F.shiftedPolynomialIdeal w k).toSubmodule
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF w k)

@[simp] theorem shiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k z : F.adaptedLieSubalgebra w) =
      F.adaptedMonomialBasis b ω hF w z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

theorem shiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (p : F.shiftedPolynomialIdeal w k) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k).repr p z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.val.1) z.val.val.2 := by
  rw [shiftedMonomialBasis, supportedSubmoduleBasis_repr, F.adaptedMonomialBasis_repr]

theorem shiftedPolynomial_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w (k + 1)).toSubmodule.comap
        (F.shiftedPolynomialIdeal w k).toSubmodule.subtype =
      Submodule.span ℚ (F.shiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  ext p
  change (∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + (k + 1))) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.shiftedMonomialBasis_repr]
    exact h z.val.val.1 z.val.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α + k ≤ ω i
    · have ha : Finsupp.weight w α ≤ ω i := (Nat.le_add_right _ _).trans hdeg
      have hz := h ⟨⟨(α, i), ha⟩, hdeg⟩ hi
      simpa only [F.shiftedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

end OAI
