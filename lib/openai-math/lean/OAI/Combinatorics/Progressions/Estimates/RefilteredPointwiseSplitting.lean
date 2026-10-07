import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership
import OAI.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
import OAI.Combinatorics.Progressions.Polynomial.SimultaneousPolynomialSymbolSplitting

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realGradedRefiltrationLayer (j : ℕ) : Submodule ℝ (ℝ ⊗[ℚ] L) :=
  (F.gradedRefiltrationLayer U j).baseChange ℝ

theorem realGradedRefiltrationLayer_antitone : Antitone (F.realGradedRefiltrationLayer U) :=
  fun _ _ hij => Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_antitone U hij)

theorem realGradedRefiltrationLayer_le (j : ℕ) :
    F.realGradedRefiltrationLayer U j ≤ (F.realLayer j).toSubmodule :=
  Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_le U j)

theorem realGradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : ℝ ⊗[ℚ] L}
    (hv : v ∈ F.realGradedRefiltrationLayer U i) (hz : z ∈ F.realGradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.realGradedRefiltrationLayer U (i + j) :=
  lie_mem_real_baseChange _ _ _ (fun _ ha _ hb => F.gradedRefiltrationLayer_lie_mem U ha hb) hv hz

theorem realGradedRefiltrationLayer_terminal : F.realGradedRefiltrationLayer U (s + 1) = ⊥ := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_terminal, Submodule.baseChange_bot]

noncomputable def realGradedRefiltrationSubalgebra : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
  realLieSubalgebraOverRat (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U))

theorem mem_realGradedRefiltrationSubalgebra (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationSubalgebra U ↔ v ∈ F.realGradedRefiltrationLayer U 1 := Iff.rfl

noncomputable def realGradedRefiltration :
    NilpotentLieFiltration (F.realGradedRefiltrationSubalgebra U) s where
  layer j := ((F.realGradedRefiltrationLayer U j).restrictScalars ℚ).comap
    (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.realGradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.realGradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℝ).mp ((F.realGradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_realGradedRefiltration_layer (j : ℕ)
    (v : F.realGradedRefiltrationSubalgebra U) :
    v ∈ (F.realGradedRefiltration U).layer j ↔
      (v : ℝ ⊗[ℚ] L) ∈ F.realGradedRefiltrationLayer U j := Iff.rfl

theorem mem_realGradedRefiltrationLayer_iff {ι : Type*} (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationLayer U j ↔ v ∈ F.realification.layer j ∧
      (F.gradedPieceProjection b ω hlayers j).baseChange ℝ v ∈ realificationLieSubalgebra U := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_eq_inf_comap b ω hlayers,
    realification_inf, realification_comap, Submodule.mem_inf, Submodule.mem_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem real_symbol_values_iff_refiltration_coefficients
    (p : F.realification.adaptedLieSubalgebra w) :
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) ↔
    ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer U (Finsupp.weight w α) := by
  refine (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).trans ?_
  apply forall_congr'
  intro α
  rw [F.mem_realGradedRefiltrationLayer_iff U b ω hlayers,
    F.realPolynomialSymbolMap_apply, F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact (and_iff_right (p.property α)).symm

theorem normalized_refiltration_coefficients_mem_first
    (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U 1 := by
  intro α
  by_cases hα : α = 0
  · rw [hα, hzero]
    exact (F.realGradedRefiltrationLayer U 1).zero_mem
  · exact F.realGradedRefiltrationLayer_antitone U (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_refiltered_polynomial_of_coefficients (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra U),
      (F.realGradedRefiltration U).Adapted w q ∧
      VectorPolynomial.map (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap q = p ∧
      coefficients q 0 = 0 := by
  have hfirst := F.normalized_refiltration_coefficients_mem_first w U hw p hp hzero
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra U).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra U _).mpr (hfirst α)
  let q := restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff
  have hq (α : σ →₀ ℕ) : (coefficients q α : ℝ ⊗[ℚ] L) = coefficients p α :=
    coefficients_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff α
  refine ⟨q, ?_, map_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff, ?_⟩
  · apply ((F.realGradedRefiltration U).adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_realGradedRefiltration_layer, hq]
    exact hp α
  · apply Subtype.ext
    exact (hq 0).trans hzero

theorem exists_pointwise_refiltered_polynomial (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hzero : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) :
    ∃ q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra U),
      (F.realGradedRefiltration U).Adapted w q ∧
      VectorPolynomial.map (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap q = p ∧
      coefficients q 0 = 0 :=
  F.exists_refiltered_polynomial_of_coefficients w U hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w U p).mp hU) hzero

theorem pointwise_refiltered_values_mem (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hzero : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) :
    ∀ t : σ → ℝ, eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U) := by
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U)).toSubmodule _).mpr
  exact F.normalized_refiltration_coefficients_mem_first w U hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w U p).mp hU) hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem normalized_symbol_polynomial_values_mem_subgroup (hw : ∀ i, 0 < w i)
    (p : (F.realification.adaptedPolynomialFiltration w).Group)
    (hzero : coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolHom b ω hlayers w p).coord) ∈ realificationLieSubalgebra U) :
    ∀ t : σ → ℝ, F.realification.polynomialOrbitRealEval w t
      (F.realification.adaptedBCHToOrbit w p) ∈
        NilpotentLieBCHGroup.realificationSubgroup (hnil := F.lowerCentralSeries_eq_bot)
          (F.gradedRefiltrationSubalgebra U) :=
  F.pointwise_refiltered_values_mem b ω hlayers w U hw p.coord hzero hU

theorem pointwise_factor_middle_refiltration (hw : ∀ i, 0 < w i)
    (g e p r : (F.realification.adaptedPolynomialFiltration w).Group)
    (hfactor : e * p * r = g)
    (hg : coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (he : coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hr : coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolHom b ω hlayers w p).coord) ∈ realificationLieSubalgebra U) :
    (∃ q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra U),
      (F.realGradedRefiltration U).Adapted w q ∧
      VectorPolynomial.map (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap q = p.coord ∧
      coefficients q 0 = 0) ∧
    (∀ t : σ → ℝ, F.realification.polynomialOrbitRealEval w t
      (F.realification.adaptedBCHToOrbit w p) ∈
        NilpotentLieBCHGroup.realificationSubgroup (hnil := F.lowerCentralSeries_eq_bot)
          (F.gradedRefiltrationSubalgebra U)) := by
  have hp : coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 :=
    (F.realification.polynomial_factor_middle_constant w g e p r hfactor he hr).trans hg
  exact ⟨F.exists_pointwise_refiltered_polynomial b ω hlayers w U hw p.coord hp hU,
    F.normalized_symbol_polynomial_values_mem_subgroup b ω hlayers w U hw p hp hU⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_pointwise_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ F.AssociatedGraded) (v : η → κ → F.AssociatedGraded),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i k, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j i) k) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, ∀ t : σ → ℝ,
        eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (P j).coord) ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
          (F.realPolynomialSymbolHom b ω hlayers w p₀).coord) ∈ realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_simultaneous_polynomial_symbol_splitting s a
  let C := max 2 (((s + 4) * (s + 3) + 2) * K)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let V := fun j => F.symbolPointwiseSubalgebra b ω hlayers w (U j)
  let v' := fun j => F.pointwiseSymbolSpanningFamily b ω hlayers w (v j)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hcount : (Fintype.card (SymbolBasisIndex w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × κ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hlayers))
    exact (Nat.cast_le.mpr hnat).trans
      (symbol_spanning_count_bound s _ _ _ hp hι hσ hκ)
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ C := by
    apply (symbol_spanning_parameter_power_bound s K hp).trans
    apply pow_le_pow_right₀ (by linarith only [hp] : 1 ≤ p + 2)
    exact le_max_right _ _
  have hcostexp := Real.exp_le_exp.mpr hcost
  have hTq : ∀ i, Real.exp ((q + 2) ^ K) ≤ T i := fun i => hcostexp.trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hP' : ∀ j, (P j).coord ∈ realificationLieSubalgebra (V j) := by
    intro j
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (U j) _).mpr (hP j)
  have hE' : ∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ a)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hlayers w T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a)
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hlayers w hw V v'
      (fun j => F.pointwiseSymbolSpanningFamily_span b ω hlayers w (U j) (hgraded j) (v j) (hspan j))
      (fun j => F.symbolPointwiseSubalgebra_blockInvariant b ω hlayers w (U j))
      H l q hH hl hq (hι.trans hpq) (hσ.trans hpq) hcount (hη.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hb
      (fun j => F.pointwiseSymbolSpanningFamily_height b ω hlayers w (v j) hH (hv j))
      T hTq g E P R hX hP' hE' hR
  refine ⟨m, e₀, p₀, r₀, hm, hmp.trans hcostexp, hlm, hepr, ?_, ?_, hr, he0, hr0, hp0⟩
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (⨅ j, U j) _).mp
    rw [F.symbolPointwiseSubalgebra_iInf]
    exact hmid
  · intro α i
    exact (he α i).trans
      (div_le_div_of_nonneg_right hcostexp (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_common_polynomial_step_drop_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b ω hF (eta j) T
        (F.realPolynomialSymbolHom b ω hF (fun _ => 1) g) p) →
      ∃ (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) ∧
        (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω (U j).toSubmodule) ∧
        (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j i) k) ≤ p) ∧
        (∀ j x, x ∈ (⨅ j, U j) → basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom b ω hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s 1
  refine ⟨2 * K, by omega, ?_⟩
  intro σ ι J L _ _ _ _ _ F b ω hF eta p hp hι hσ hJ hstructure T hT g hfactor
  classical
  choose m E P R U v hm hmp hprod hE hR hv hU hheight hfreq hP using hfactor
  let l := ∏ j, m j
  have hl : 0 < l := Finset.prod_pos (fun j _ => hm j)
  have hdvd (j : J) : m j ∣ l := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let q := p ^ 2 + p + 2
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hq : 0 ≤ q := hp.trans hpq
  have hq1 : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ (2 * K) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    nlinarith
  have hlq : (l : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget m hp hJ hmp).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hq1)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : ∀ j, F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp ((q + 2) ^ 1)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hF (fun _ => 1) T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using hpq.trans (by linarith : q ≤ q + 2))
  have hrat : ∀ j, F.SymbolRationalGrid b ω hF (fun _ => 1) l (R j) :=
    fun j => F.symbolRationalGrid_mono b ω hF (fun _ => 1) (hm j) (hdvd j) (R j) (hR j)
  obtain ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q, _, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) U v hv hU H l q hH hl hq
      (hι.trans hpq) (hσ.trans hpq) (hι.trans hpq) (hJ.trans hpq) hHq hlq
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun j i k => rationalHeightLE_ceil_exp (hheight j i k)) T
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)) g E P R hprod
      (fun j => (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) (U j) _).mp (hP j))
      hslow hrat
  refine ⟨U, v, m₀, e₀, p₀, r₀, hv, hU, hheight, ?_, hm₀,
    hm₀q.trans (Real.exp_le_exp.mpr hcost), hepr, hmid, ?_, hr, he0, hr0, hp0⟩
  · intro j x hx hxgrade
    exact hfreq j x ((lieSubalgebra_mem_iInf U x).mp hx j) hxgrade
  · intro α i
    exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
      (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_pointwise_refiltered_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ F.AssociatedGraded) (v : η → κ → F.AssociatedGraded),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i k, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j i) k) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
      ∀ E P R : η → F.RealPolynomialSymbolGroup w,
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, ∀ t : σ → ℝ,
        eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (P j).coord) ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra (⨅ j, U j))),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (F.realGradedRefiltration (⨅ j, U j)).Adapted w q ∧
        VectorPolynomial.map (F.realGradedRefiltrationSubalgebra (⨅ j, U j)).incl.toLinearMap q = p₀.coord ∧
        coefficients q 0 = 0 ∧
        (∀ t : σ → ℝ, F.realification.polynomialOrbitRealEval w t
          (F.realification.adaptedBCHToOrbit w p₀) ∈
            NilpotentLieBCHGroup.realificationSubgroup (hnil := F.lowerCentralSeries_eq_bot)
              (F.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  obtain ⟨C, hC, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g hg E P R hX hP hE hR
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, hmid, he, hr, he0, hr0, _⟩ :=
    hsplit F b ω hlayers w hw U v hspan hgraded H l p hH hl hp hι hσ hκ hη hHp hlp hb hv
      T hT g E P R hX hP hE hR
  obtain ⟨⟨q, hq, hmap, hq0⟩, hvalues⟩ :=
    F.pointwise_factor_middle_refiltration b ω hlayers w (⨅ j, U j) hw
      g e₀ p₀ r₀ hepr hg he0 hr0 hmid
  exact ⟨m, e₀, p₀, r₀, q, hm, hmp, hlm, hepr, hq, hmap, hq0, hvalues, he, hr, he0, hr0⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
