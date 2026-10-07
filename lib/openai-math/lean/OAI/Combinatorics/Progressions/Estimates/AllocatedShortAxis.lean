import OAI.Combinatorics.Progressions.Geometry.AllocatedArraySupport
import OAI.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale

namespace OAI

section

namespace Erdos3

noncomputable def tailAxisInterpolation {V : Type*} (T : V → ℝ) (K L s : ℕ) (ε : ℝ)
    (e : V →₀ ℕ) : ℝ → ℝ :=
  if L^(s+1) < K then normalizedIntegerInterpolation K 0 (ε / monomialScale T e)
  else integerMassTent K 0

noncomputable def tailAxisInterpolationCap (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (L : ℝ)^s / ε) ((L : ℝ)^(s+1))

noncomputable def tailAxisInterpolationLip (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2)
    (2 * ((L : ℝ)^(s+1))^2)

theorem tailAxisInterpolation_spec {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    IsIntegerMassInterpolation K (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he)
      (tailAxisInterpolationCap L s ε) (tailAxisInterpolationLip L s ε)
      (tailAxisInterpolation T K L s ε e) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hS := monomialScale_pos T hT e
  have hSL := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (show (1 : ℝ) ≤ L by exact_mod_cast hL) hTL e he
  by_cases ha : L^(s+1) < K
  · simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 (ε / monomialScale T e) hKr
      (div_pos hε hS) (integerAxisTail_width T hT hL hTL hε hεL e he ha)).mono
    · apply le_trans _ (le_max_left _ _)
      calc
        2 / (ε / monomialScale T e) = 2 * monomialScale T e / ε := by field_simp
        _ ≤ 2 * (L : ℝ)^s / ε := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSL (by norm_num)) hε.le
    · apply le_trans _ (le_max_left _ _)
      calc
        2 * (probabilityProfileLipschitz : ℝ) / (ε / monomialScale T e)^2 =
            2 * (probabilityProfileLipschitz : ℝ) * (monomialScale T e)^2 / ε^2 := by field_simp
        _ ≤ 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hS.le hSL 2) (by positivity)) (sq_nonneg ε)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^(s+1) := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (integerMassTent_spec K hKr 0).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)

noncomputable def allocatedProjectionPMFs : Fin n → J → PMF ℤ :=
  fun i => allocatedIntegerPolynomialCoordinatePMF (Pz i) j₀ h (basisAxisScale b i) L s
    hh (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ (hgap i) hεL

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

variable (Pc : I → Finset J)

noncomputable def allocatedMixedArrayLaw : Measure ((I → J → ℝ) × (Fin n → J → ℤ)) :=
  independentPolynomialLaw
    (fun i => realDensityMeasure volume (continuousPolynomialDensity e T (Pc i) j₀ R σ))
    (fun i => Measure.pi (fun j => (intLaws i j).toMeasure))

local notation "source" => allocatedMixedArrayLaw W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL Pc

theorem allocatedMixedArrayLaw_probability : IsProbabilityMeasure source := by
  let : ∀ i, IsProbabilityMeasure
      (realDensityMeasure volume (continuousPolynomialDensity e T (Pc i) j₀ R σ)) :=
    fun i => continuousPolynomialDensity_probability e T (fun v => lt_of_lt_of_le zero_lt_one (hT v))
      (Pc i) j₀ hR hσ
  exact independentPolynomialLaw_probability _ _

theorem allocatedMixedArray_quotient_density
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4) :
    ∃ F : (J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ,
      Measurable F ∧ (∀ y, 0 ≤ F y) ∧ Integrable F (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, F y ∂Measure.pi (fun _ : J => μ)) = 1 ∧
      Measure.map (mixedArrayQuotient W b hb o) source = realDensityMeasure (Measure.pi (fun _ : J => μ)) F := by
  refine scaledArray_quotient_density W b hb o μ e T hT
    (fun i => coefficientProfileCenter (Pc i) (principalProfileSize R (Pc i).card))
    (fun i => coefficientProfileWidth (Pc i) j₀ (R / 4) (principalProfileSize R (Pc i).card)
      (tailProfileSize R σ (Fintype.card J)))
    (fun i => continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ) intLaws hC hR.le hchart hsmall ?_ ?_
  · intro i j
    exact (allocatedProfile_term_bound (Pc i) j₀ (hc₀ i) hR hσ hσ1 j).trans (by linarith)
  · intro i j k hk
    have hb' := allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s
      hh (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
      R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk
    exact hb'.trans (by linarith)

theorem allocatedMixedArray_ae_chart (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4) :
    ∀ᵐ p ∂source, ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
      mixedPolynomialPoint W b o e p.1 p.2 x ∈ standardLatticeSmallBox D := by
  let : ∀ i, IsProbabilityMeasure
      (realDensityMeasure volume (continuousPolynomialDensity e T (Pc i) j₀ R σ)) :=
    fun i => continuousPolynomialDensity_probability e T (fun v => lt_of_lt_of_le zero_lt_one (hT v))
      (Pc i) j₀ hR hσ
  refine independentPolynomialLaw_ae_chart W b o e T _ _ hC hR.le hchart hsmall ?_ ?_
  · intro i
    have hb' := continuousPolynomialDensity_ae_box e T (fun v => lt_of_lt_of_le zero_lt_one (hT v))
      (Pc i) j₀ (hc₀ i) hR hσ hσ1
    filter_upwards [hb'] with a ha
    intro x hx
    exact (ha x hx).trans (by linarith)
  · intro i
    have hb' := allocatedIntegerPolynomial_ae_box (Pz i) j₀ h (basisAxisScale b i) L s
      hh (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
      R σ hR hσ (hgap i) hεL (hz₀ i) he₀ hσ1 (hprincipal i)
    filter_upwards [hb'] with a ha
    intro x hx
    exact (ha x hx).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def allocatedArrayCenters {I J V : Type*} (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (R : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileCenter (Pc i) (principalProfileSize R (Pc i).card) j / monomialScale T (e j)

noncomputable def allocatedArrayWidths {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (j₀ : J) (R σ : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileWidth (Pc i) j₀ (R / 4) (principalProfileSize R (Pc i).card)
    (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)

theorem allocatedArrayWidths_pos {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 0 < T v) (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    (i : I) (j : J) : 0 < allocatedArrayWidths e T Pc j₀ R σ i j :=
  div_pos (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j) (monomialScale_pos T hT (e j))

theorem allocatedArrayProfiles_bound {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 1 ≤ T v) (Pc : I → Finset J) (j₀ : J) (hc₀ : ∀ i, j₀ ∉ Pc i)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (i : I) (j : J) :
    |allocatedArrayCenters e T Pc R i j| + allocatedArrayWidths e T Pc j₀ R σ i j ≤ R := by
  apply scaledProfile_div_bound (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j).le
    (one_le_monomialScale T hT (e j))
  exact (allocatedProfile_term_bound (Pc i) j₀ (hc₀ i) hR hσ hσ1 j).trans (by linarith)

theorem allocatedArraySupported_iff_rows {I Z J V : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (Pc : I → Finset J) (j₀ : J) (R σ : ℝ)
    (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) p x ↔
      (∀ i, continuousPolynomialDensity e T (Pc i) j₀ R σ (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) :=
  mixedArraySupported_iff_rows _ _ _ _

theorem allocatedArrayLaw_rows {I J V : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (Pc : I → Finset J) (j₀ : J)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (p : Fin n → J → PMF ℤ) :
    independentPolynomialLaw
      (fun i => realDensityMeasure volume (continuousPolynomialDensity e T (Pc i) j₀ R σ))
      (fun i => Measure.pi (fun j => (p i j).toMeasure)) =
    mixedScalarArrayLaw (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) p :=
  scaledArrayLaw_rows e T hT _ _ (fun i => continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ) p

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_chart (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  apply mixedCoefficient_small_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

theorem allocatedArraySupported_polynomial_chart (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (ha : mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) intLaws a)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    mixedPolynomialPoint W b o e a.1 a.2 x ∈ standardLatticeSmallBox D := by
  have hs := (allocatedArraySupported_iff_rows e T Pc j₀ R σ intLaws a).mp ha
  apply mixedPolynomialPoint_small W b o e a.1 a.2 x hC hR.le hchart hsmall
  · intro i
    exact (continuousPolynomialDensity_box e T (fun v => lt_of_lt_of_le zero_lt_one (hT v))
      (Pc i) j₀ (hc₀ i) hR hσ hσ1 (hs.1 i) x hx).trans (by linarith)
  · intro i
    exact (allocatedIntegerPolynomial_box (Pz i) j₀ h (basisAxisScale b i) L s hh
      (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
      R σ hR hσ (hgap i) hεL (hz₀ i) he₀ hσ1 (hprincipal i) (a.2 i) (hs.2 i) x hx).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

noncomputable def allocatedWidthFloor (R σ : ℝ) (L s a : ℕ) : ℝ :=
  min (R / 4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)) / (L : ℝ)^s

theorem allocatedWidthFloor_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L : ℕ} (hL : 0 < L) (s a : ℕ) : 0 < allocatedWidthFloor R σ L s a := by
  unfold allocatedWidthFloor
  exact div_pos (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR a) (by norm_num)) (tailProfileSize_pos hR hσ a)))
    (pow_pos (Nat.cast_pos.mpr hL) _)

theorem allocatedArrayWidths_floor {I J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L)
    (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) (i : I) (j : J) :
    allocatedWidthFloor R σ L s (Fintype.card J) ≤ allocatedArrayWidths e T Pc j₀ R σ i j := by
  classical
  let a := min (R / 4)
    (min (principalProfileSize R (Fintype.card J) / 2) (tailProfileSize R σ (Fintype.card J)))
  have ha : 0 ≤ a := le_of_lt (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR _) (by norm_num)) (tailProfileSize_pos hR hσ _)))
  have hprincipal : principalProfileSize R (Fintype.card J) ≤ principalProfileSize R (Pc i).card := by
    unfold principalProfileSize
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    gcongr
    exact_mod_cast (Pc i).card_le_univ
  have haWidth : a ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
      (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j := by
    unfold coefficientProfileWidth
    split_ifs
    · exact min_le_left _ _
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        (div_le_div_of_nonneg_right hprincipal (by norm_num))
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hmono := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (by exact_mod_cast hL) hTL (e j) (he j)
  have hscale := monomialScale_pos T hT (e j)
  change a / (L : ℝ)^s ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
    (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)
  exact (div_le_div_of_nonneg_left ha hscale hmono).trans
    (div_le_div_of_nonneg_right haWidth hscale.le)

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_power_bounds (a : ℕ) {R σ X : ℝ}
    (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) :
    (R / 4)⁻¹ ≤ X^2 ∧ (principalProfileSize R a)⁻¹ ≤ X^3 ∧
      (principalProfileSize R a / 2)⁻¹ ≤ X^4 ∧ (tailProfileSize R σ a)⁻¹ ≤ X^4 := by
  have hX0 : 0 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hp0 : 0 ≤ (principalProfileSize R a)⁻¹ := inv_nonneg.mpr (principalProfileSize_pos hR a).le
  have hprincipal : (principalProfileSize R a)⁻¹ ≤ X^3 := by
    unfold principalProfileSize
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨?_, hprincipal, ?_, ?_⟩
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X := by gcongr
      _ = _ := by ring
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X^3 := by gcongr
      _ = _ := by ring
  · unfold tailProfileSize
    rw [inv_div, div_eq_mul_inv, mul_inv_rev]
    calc
      _ ≤ X * X * (X * X) := by gcongr
      _ = _ := by ring

theorem allocatedWidthFloor_inverse_power_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ X : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) (hLX : (L : ℝ) ≤ X) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ X^(m+4) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨hρ, _, hγ, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX hRX hσX haX
  have hmin : (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ ≤ X^4 :=
    inv_min_le_of_inv_le (hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)))
      (inv_min_le_of_inv_le hγ hε)
  have hLs : (L : ℝ)^s ≤ X^m :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hLX s).trans (pow_le_pow_right₀ hX1 hs)
  have hγ0 := (principalProfileSize_pos hR a).le
  have hε0 := (tailProfileSize_pos hR hσ a).le
  have hmin0 : 0 ≤ (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ := by
    positivity
  rw [allocatedWidthFloor, inv_div, div_eq_mul_inv]
  calc
    _ ≤ X^m * X^4 := by gcongr
    _ = _ := (pow_add _ _ _).symm

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_exp_bounds (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ) ≤ P) :
    (R / 4)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a / 2)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (tailProfileSize R σ a)⁻¹ ≤ Real.exp (4 * (P + 8)) := by
  let X := Real.exp (P + 8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hX1 : 1 ≤ X := by linarith
  have haX : (a : ℝ) + 1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ) + 1 ≤ Real.exp P).trans hPX
  obtain ⟨hρ, hγ, hγ2, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX
  have he : X^4 = Real.exp (4*(P+8)) := by simp only [X, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [← he]
  exact ⟨hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)),
    hγ.trans (pow_le_pow_right₀ hX1 (by norm_num)), hγ2, hε⟩

theorem allocatedWidthFloor_inverse_exp_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ P : ℝ} (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P)
    (haP : (a : ℝ) ≤ P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ Real.exp (((m : ℝ)+4)*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have haX : (a : ℝ)+1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ)+1 ≤ Real.exp P).trans hPX
  have h := allocatedWidthFloor_inverse_power_bound L s m a hs hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX (hLP.trans hPX)
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def allocatedScaleLog (P : ℝ) : ℝ := (1+P^2)*(5*P+49)

theorem allocatedScaleLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScaleLog P := by
  unfold allocatedScaleLog
  positivity

theorem le_allocatedScaleLog {P : ℝ} (hP : 0 ≤ P) : P ≤ allocatedScaleLog P := by
  have h : 0 ≤ P^2*(5*P+49) := by positivity
  unfold allocatedScaleLog
  nlinarith

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerSamplerWidths_inverse_exp_bounds (R σ : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P) :
    (∀ j, (layerSamplerTailWidth (G := G) B R σ j)⁻¹ ≤ Real.exp (4*(P+8))) ∧
      (∀ a, (layerSamplerGapWidth (G := G) B R a)⁻¹ ≤ Real.exp (4*(P+8))) := by
  constructor
  · intro j
    exact (allocatedProfile_inverse_exp_bounds _ hP (hR j) (hσ j) (hRP j) (hσP j) (hcount j)).2.2.2
  · intro a
    have hc : ((layerIntegerPrincipalSlots (G := G) B a.1 a.2).card : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcount a.1)
    exact (allocatedProfile_inverse_exp_bounds _ hP (hR a.1) (hσ a.1)
      (hRP a.1) (hσP a.1) hc).2.1

theorem layerSamplerScaleBound_exp (R σ : Fin m → ℝ) (L₀ : ℕ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    (layerSamplerScaleBound (G := G) B R σ L₀ : ℝ) ≤ Real.exp (allocatedScaleLog P) := by
  obtain ⟨ht, hg⟩ := layerSamplerWidths_inverse_exp_bounds B R σ hP hR hσ hRP hσP hcount
  have hinit := commonPolynomialInitialScale_exp_bound (layerSamplerTailWidth (G := G) B R σ) L₀
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) hP (by positivity) hA ht hL₀
  have hgap := commonPolynomialGapRatio_exp_bound (layerSamplerGapWidth (G := G) B R)
    (fun a => principalProfileSize_pos (hR a.1) _) hP (by positivity) hA hg
  have haxes : (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ P^2 := by
    calc
      _ = ∑ j : Fin m, (n j : ℝ) := by simp [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ)*P := by simp
      _ ≤ P^2 := by nlinarith
  have hp := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hgap (by positivity)
    (Fintype.card (Σ j : Fin m, Fin (n j))) haxes
  simp only [layerSamplerScaleBound, Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (P+4*(P+8)+17) * Real.exp (P^2*(P+4*(P+8)+17)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedScaleLog; ring

theorem selectedLayerSamplerScale_exp_bound
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    ((selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value : ℝ) ≤
      Real.exp (allocatedScaleLog P) :=
  (Nat.cast_le.mpr (selectedLayerSamplerScale_bounds B U b R σ hR hσ L₀).2).trans
    (layerSamplerScaleBound_exp B R σ L₀ hP hm hn hR hσ hRP hσP hcount hA hL₀)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem heterogeneousSamplerSides_long_or_bounded {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) (γ : D → ℝ)
    {L T : ℕ} (hT : 0 < T) (hTL : T ≤ L) (v : SamplerTupleIndex G B h) :
    T ≤ heterogeneousSamplerSides h K L γ v ∨
      ∃ (d : D) (b : B d) (r : Fin (h d)) (k : ℕ),
        v = .inr ⟨d, b, r⟩ ∧ K d = some k ∧ k ≤ integerAxisShortBound (h d) T (γ d) := by
  rcases v with g | ⟨d, b, r⟩
  · exact Or.inl hTL
  · cases hk : K d with
    | none =>
      left
      simpa only [heterogeneousSamplerSides, hk] using hTL
    | some k =>
      rcases integerAxisSideLength_long_or_bounded (K := k) (γ := γ d) (hh d) hT hTL with hl | hs
      · left
        simpa only [heterogeneousSamplerSides, hk] using hl
      · exact Or.inr ⟨d, b, r, k, rfl, hk, hs⟩

namespace VectorPolynomial

theorem selectedLayerSampler_integer_side_dichotomy {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) {T : ℕ} (hT : 0 < T) (hTL : T ≤ L₀) {P t : ℝ}
    (hP : 0 ≤ P) (ht : 0 ≤ t) (hTt : (T : ℝ) ≤ Real.exp t)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (j : Fin m) (i : Fin (n j)) (b : B ⟨j, .inr i⟩) (r : Fin (j.val+1)) :
    let S := selectedLayerSamplerScale (G := G) B U basis R σ hR hσ L₀
    T ≤ layerSamplerSides (G := G) B U basis R S.value (.inr ⟨⟨j, .inr i⟩, b, r⟩) ∨
      (basisAxisScale (basis j) i : ℝ) ≤ Real.exp (4*(P+8)+2+m*(t+1)) := by
  let S := selectedLayerSamplerScale (G := G) B U basis R σ hR hσ L₀
  let γ := principalProfileSize (R j) (Fintype.card (B ⟨j, .inr i⟩))
  have hγ : 0 < γ := principalProfileSize_pos (hR j) _
  have hγP : γ⁻¹ ≤ Real.exp (4*(P+8)) := by
    have hg := (layerSamplerWidths_inverse_exp_bounds (G := G) B R σ hP hR hσ hRP hσP hcount).2 ⟨j, i⟩
    simpa only [layerSamplerGapWidth, layerIntegerPrincipalSlots_card] using hg
  have hTS : T ≤ S.value := hTL.trans (selectedLayerSamplerScale_bounds B U basis R σ hR hσ L₀).1
  change T ≤ integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value γ ∨ _
  rcases integerAxisSideLength_long_or_bounded (γ := γ) (K := basisAxisScale (basis j) i)
    (Nat.zero_lt_succ _) hT hTS with hl | hs
  · exact Or.inl hl
  · right
    calc
      (basisAxisScale (basis j) i : ℝ) ≤ integerAxisShortBound (j.val+1) T γ := by exact_mod_cast hs
      _ ≤ Real.exp (4*(P+8)+2+(j.val+1)*(t+1)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          integerAxisShortBound_le_exp (j.val+1) T hγ (by positivity) hγP hTt
      _ ≤ Real.exp (4*(P+8)+2+m*(t+1)) := by
        apply Real.exp_le_exp.mpr
        have hj : ((j.val+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast j.isLt
        push_cast at hj
        nlinarith

end VectorPolynomial
end Erdos3

end

end OAI
