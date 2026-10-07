/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.RealDualRationalBounds
import OAI.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialConstantHom :
    (F.adaptedPolynomialFiltration w).Group →* F.Group :=
  NilpotentLieBCHGroup.map ((evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra w).incl)

@[simp] theorem adaptedPolynomialConstantHom_coord
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialConstantHom w g).coord =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 :=
  eval_zero_eq_coefficient _

theorem polynomial_factor_middle_constant
    (g e p r : (F.adaptedPolynomialFiltration w).Group) (h : e * p * r = g)
    (he : coefficients (e.coord : VectorPolynomial σ ℚ L) 0 = 0)
    (hr : coefficients (r.coord : VectorPolynomial σ ℚ L) 0 = 0) :
    coefficients (p.coord : VectorPolynomial σ ℚ L) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 := by
  have he' : F.adaptedPolynomialConstantHom w e = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, he]
  have hr' : F.adaptedPolynomialConstantHom w r = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, hr]
  have h' := congrArg (F.adaptedPolynomialConstantHom w) h
  rw [map_mul, map_mul, he', hr', one_mul, mul_one] at h'
  have hc := congrArg NilpotentLieBCHGroup.coord h'
  simpa only [F.adaptedPolynomialConstantHom_coord] using hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedConstantLieHom : L →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w where
  toFun := F.adaptedConstant w
  map_add' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _
  map_lie' {a b} := by
    apply Subtype.ext
    change monomial 0 ⁅a, b⁆ = ⁅monomial 0 a, monomial 0 b⁆
    rw [lie_monomial, zero_add]

noncomputable def adaptedConstantGroupHom : F.Group →* (F.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.adaptedConstantLieHom w)

@[simp] theorem adaptedConstantGroupHom_log (g : F.Group) :
    ((F.adaptedConstantGroupHom w g).coord : VectorPolynomial σ ℚ L) = monomial 0 g.coord := rfl

@[simp] theorem adaptedPolynomialConstantHom_constant (g : F.Group) :
    F.adaptedPolynomialConstantHom w (F.adaptedConstantGroupHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialConstantHom_coord, F.adaptedConstantGroupHom_log,
    coefficients_monomial, Finsupp.single_eq_same]

@[simp] theorem polynomialSymbolHom_constant (g : F.Group) :
    F.polynomialSymbolHom w (F.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.polynomialSymbolMap_constant w g.coord

theorem exists_constant_normalized_polynomial
    (g : (F.adaptedPolynomialFiltration w).Group) (r γ : F.Group)
    (hg : F.adaptedPolynomialConstantHom w g = r * γ) :
    ∃ q : (F.adaptedPolynomialFiltration w).Group,
      F.adaptedConstantGroupHom w r * q * F.adaptedConstantGroupHom w γ = g ∧
      coefficients (q.coord : VectorPolynomial σ ℚ L) 0 = 0 ∧
      F.polynomialSymbolHom w q = F.polynomialSymbolHom w g := by
  let c := F.adaptedConstantGroupHom w
  let q := c r⁻¹ * g * c γ⁻¹
  have hq : F.adaptedPolynomialConstantHom w q = 1 := by
    simp only [q, c, map_mul, F.adaptedPolynomialConstantHom_constant, hg]
    simp
  refine ⟨q, ?_, ?_, ?_⟩
  · simp [q, c, mul_assoc]
  · have hc := congrArg NilpotentLieBCHGroup.coord hq
    simpa only [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one] using hc
  · simp only [q, c, map_mul, F.polynomialSymbolHom_constant, one_mul, mul_one]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialRationalGrid (l : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid l

theorem polynomialRationalGrid_of_dvd {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) : F.PolynomialRationalGrid b w m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

theorem polynomialRationalGrid_constant (l : ℕ) (c : F.realification.Group)
    (hc : (fun i => (b.baseChange ℝ).repr c.coord i) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid b w l (F.realification.adaptedConstantGroupHom w c) := by
  classical
  obtain ⟨a, ha⟩ := hc
  refine ⟨fun z => if z.1 = 0 then a z.2 else 0, ?_⟩
  funext z
  change ((if z.1 = 0 then a z.2 else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.adaptedConstantGroupHom w c).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases h : z.1 = 0
  · simpa only [h, ite_true, Finsupp.single_eq_same, Pi.smul_apply, smul_eq_mul] using congrFun ha z.2
  · simp only [h, ite_false, Int.cast_zero, Finsupp.single_eq_of_ne h, map_zero,
      Finsupp.zero_apply, mul_zero]

theorem polynomialRationalGrid_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) ↔
      (fun z : AdaptedBasisIndex w ω =>
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z) ∈ realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a z.val, ?_⟩
    funext z
    have hz := congrFun ha z.val
    change (a z.val : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realAdaptedPolynomialGroupHom w g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 at hz
    rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
    funext z
    change ((if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
      (l : ℝ) * (b.baseChange ℝ).repr (coefficients
        ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
    by_cases h : Finsupp.weight w z.1 ≤ ω z.2
    · rw [dite_eq_left h, F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨z, h⟩]
      exact congrFun ha ⟨z, h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property z.1) z.2 h
      rw [dite_eq_right h, Int.cast_zero, hz, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialSlowBound (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  ∀ α i, |(b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ M / monomialScale T α

theorem polynomialSlowBound_inv_iff (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g⁻¹ ↔ F.PolynomialSlowBound b w T M g := by
  change (∀ α i, |(b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α) i| ≤ M / monomialScale T α) ↔ _
  simp only [map_neg, Finsupp.neg_apply, abs_neg, PolynomialSlowBound]

theorem polynomialSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) : F.PolynomialSlowBound b w T N g := by
  intro α i
  exact (hg α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

theorem polynomialSlowBound_constant (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (c : F.realification.Group)
    (hc : ∀ i, |(b.baseChange ℝ).repr c.coord i| ≤ M) :
    F.PolynomialSlowBound b w T M (F.realification.adaptedConstantGroupHom w c) := by
  classical
  intro α i
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simpa only [Finsupp.single_eq_same, monomialScale_zero, div_one] using hc i
  · rw [Finsupp.single_eq_of_ne hα, map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialSlowBound_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) ↔
      ∀ z : AdaptedBasisIndex w ω,
        |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
          M / monomialScale T z.val.1 := by
  constructor
  · intro hg z
    rw [← F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z]
    exact hg z.val.1 z.val.2
  · intro hg α i
    by_cases h : Finsupp.weight w α ≤ ω i
    · rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨(α, i), h⟩]
      exact hg ⟨(α, i), h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property α) i h
      rw [hz, abs_zero]
      exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realAdapted_factor_middle_constant
    (g a b c : F.RealAdaptedPolynomialGroup w) (h : a * b * c = g)
    (ha : coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0)
    (hc : coefficients (F.realAdaptedPolynomialMap w c.coord) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap w b.coord) 0 =
      coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  have hp : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w b *
      F.realAdaptedPolynomialGroupHom w c = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, h]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w b) (F.realAdaptedPolynomialGroupHom w c) hp ha hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_polynomial_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
        (∀ r ∈ rs, F.PolynomialRationalGrid b w l r) → F.PolynomialRationalGrid b w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, ?_⟩
  intro rs hlen hrs
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, (B.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    apply (F.polynomialRationalGrid_groupHom_iff b w ω hlayers l _).mp
    rw [F.realAdaptedPolynomialGroupHom_lift]
    exact hrs u hu
  have hout := (F.polynomialRationalGrid_groupHom_iff b w ω hlayers m ys.prod).mpr
    (hprod ys (by simpa only [ys, List.length_map] using hlen) hinput)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem linearPolynomial_adapted (a : σ → L) :
    linearPolynomial (R := ℚ) a ∈ F.adaptedLieSubalgebra (fun _ => 1) := by
  intro α
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul, F.one_eq_top, Submodule.mem_top]
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h)]
    exact Submodule.zero_mem _

noncomputable def linearPolynomialGroup (a : σ → L) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  ⟨⟨linearPolynomial a, F.linearPolynomial_adapted a⟩⟩

@[simp] theorem linearPolynomialGroup_log (a : σ → L) :
    ((F.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ L) = linearPolynomial a := rfl

theorem stepOne_lie_eq_zero (F : NilpotentLieFiltration L 1) (a b : L) : ⁅a, b⁆ = 0 := by
  have ha : a ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hb : b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem ha hb
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem stepOne_coord_mul (F : NilpotentLieFiltration L 1) (a b : F.Group) :
    (a * b).coord = a.coord + b.coord :=
  lieBCH_eq_add_of_lie_eq_zero F.lowerCentralSeries_eq_bot (F.stepOne_lie_eq_zero a.coord b.coord)

theorem polynomialSlowBound_linear (b : Basis ι ℚ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] L) (ha : ∀ i j, |(b.baseChange ℝ).repr (a i) j| ≤ M / T i) :
    F.PolynomialSlowBound b (fun _ => 1) T M (F.realification.linearPolynomialGroup a) := by
  classical
  intro α j
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simpa [monomialScale] using ha i j
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_linear (b : Basis ι ℚ L) (m : ℕ) (a : σ → ℝ ⊗[ℚ] L)
    (ha : (fun z : σ × ι => (b.baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid m) :
    F.PolynomialRationalGrid b (fun _ => 1) m (F.realification.linearPolynomialGroup a) := by
  classical
  obtain ⟨n, hn⟩ := ha
  refine ⟨fun z => if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0, ?_⟩
  funext z
  change ((if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0 : ℤ) : ℝ) =
    (m : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = z.1
  · rw [dite_eq_left h]
    have hc := coefficients_linearPolynomial_single (R := ℚ) a h.choose
    rw [h.choose_spec] at hc
    rw [hc]
    exact congrFun hn (h.choose, z.2)
  · rw [dite_eq_right h, Int.cast_zero,
      coefficients_linearPolynomial_of_ne a z.1 (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_polynomial_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
      (∀ r ∈ rs, F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) r) →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
  let E := F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealAdaptedMonomialBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hslow : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a))
        (F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers u)) := by
      rw [F.realAdaptedPolynomialGroupHom_lift]
      exact hrs u hu
    have hz := (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mp hslow z
    have hscaled := (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mpr hz
    exact hscaled.trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  have hout : F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
      (F.realAdaptedPolynomialGroupHom w ys.prod) := by
    apply (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mpr
    intro z
    apply (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mp
    exact (hK E (lieStructureConstants B) H q
      (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot ys hstruct hq hdim
      (by simpa only [ys, List.length_map] using hlen) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hheight hinput z).trans (Real.exp_le_exp.mpr hpoly)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def affinePolynomialOrbit (b : L) (a : σ → L) :
    F.PolynomialOrbit (fun _ : σ => 1) :=
  polynomialOrbitOfLog (monomial 0 b + linearPolynomial a) (by
    apply (F.mem_adaptedSubmodule _ _).mp
    exact (F.adaptedSubmodule _).add_mem
      ((F.mem_adaptedSubmodule _ _).mpr (F.adapted_constant _ b))
      (F.linearPolynomial_adapted a))

@[simp] theorem affinePolynomialOrbit_log (b : L) (a : σ → L) :
    (F.affinePolynomialOrbit b a).log = monomial 0 b + linearPolynomial a := rfl

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

theorem affinePolynomialOrbit_real_coord (b : L) (a : σ → L) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, x j • a j := by
  rw [polynomialOrbitRealEval_coord, affinePolynomialOrbit_log, map_add,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

theorem affinePolynomialOrbit_integer_coord (b : L) (a : σ → L) (x : σ → ℤ) :
    (F.polynomialOrbitEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  rw [← F.polynomialOrbitRealEval_integer]
  exact F.affinePolynomialOrbit_real_coord b a _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientBound (T : σ → ℝ) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  ∀ z : AdaptedBasisIndex w ω,
    |((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z| ≤ M / monomialScale T z.val.1

theorem realAdaptedCoefficientBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientBound b ω hF w T M x) :
    F.RealAdaptedCoefficientBound b ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

theorem realAdaptedCoefficientBound_scaled_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      ∀ z, |(F.scaledRealAdaptedMonomialBasis b ω hF w T hT).repr x z| ≤ M := by
  simp only [RealAdaptedCoefficientBound, F.scaledRealAdaptedMonomialBasis_bound_iff]

theorem realAdaptedCoefficientBound_polynomial_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientBound b ω hF w T M g.coord ↔
      F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialSlowBound_groupHom_iff b w ω hF T hT hM g).symm

theorem exists_scaled_polynomial_dual_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ z : DualGroup (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot,
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualBaseLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualTangentLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualLogDerivative z)) ∧
      (∀ (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w),
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) g.coord →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualAdjoint g x)) := by
  have hdualExists := exists_dual_coordinate_operation_bound s a
  obtain ⟨D, _, hdual⟩ := hdualExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl (2 : ℝ))) a)
  let E := F.scaledRealAdaptedMonomialBasis b ω hF w T hT
  have hoperations := hdual E (lieStructureConstants (F.adaptedMonomialBasis b ω hF w)) H q
    (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot
    (fun i j k => (F.scaledRealAdaptedMonomialBasis_structure b ω hF w T hT i j k).symm)
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF w hH hc)
  have hin (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x) :
      ∀ z, |E.repr x z| ≤ Real.exp ((q + 2) ^ a) :=
    fun z => ((F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mp hx z).trans hinput
  have hout (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : ∀ z, |E.repr x z| ≤ Real.exp ((q + D) ^ D)) :
      F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) x := by
    apply (F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mpr
    exact fun z => (hx z).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hb ht
    exact hout _ (hoperations.1 z (hin _ hb) (hin _ ht))
  · intro g x hg hx
    exact hout _ (hoperations.2 g x (hin _ hg) (hin _ hx))

end Erdos3.NilpotentLieFiltration

end

end OAI
