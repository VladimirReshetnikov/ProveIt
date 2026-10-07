import OAI.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
import OAI.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem forecast_single_cutoff_error {T : Type*} [Fintype T]
    (target cutoff : ℂ) (coefficient atom : T → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hcutoff : ‖cutoff‖ ≤ 1)
    (hkeep : target ≠ 0 → cutoff = 1)
    (herror : cutoff ≠ 0 → ‖target - ∑ i, coefficient i * atom i‖ ≤ ε) :
    ‖target - ∑ i, coefficient i * (cutoff * atom i)‖ ≤ ε := by
  simpa only [Finset.univ_unique, Finset.prod_singleton] using
    finite_site_cutoff_error target coefficient (fun i (_ : Unit) => atom i)
      (fun _ : Unit => cutoff) hε (fun _ => hcutoff)
      (fun ht _ => hkeep ht) (fun ht => by
        simpa only [Finset.univ_unique, Finset.prod_singleton] using herror (ht ()))

theorem forecast_buffered_chart_twist_expansion
    {X Y T : Type*} [Fintype T]
    (q : X → Y) (region : Set X) (hinj : Set.InjOn q region)
    (source cutoff : X → ℂ) (coefficient : T → ℂ) (atom : T → X → ℂ)
    (scale : T → ℂ) (twist : T → Y → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hcutoff : ∀ x ∈ region, ‖cutoff x‖ ≤ 1)
    (hkeep : ∀ x ∈ region, source x ≠ 0 → cutoff x = 1)
    (herror : ∀ x ∈ region, cutoff x ≠ 0 →
      ‖source x - ∑ i, coefficient i * atom i x‖ ≤ ε)
    (htwist : ∀ i y, restrictedComplexChartDensity q region 1
      (fun x => cutoff x * atom i x) y = scale i * twist i y) :
    ∀ y, ‖restrictedComplexChartDensity q region 1 source y -
      ∑ i, (coefficient i * scale i) * twist i y‖ ≤ ε := by
  intro y
  have heq : (∑ i, (coefficient i * scale i) * twist i y) =
      restrictedComplexChartDensity q region 1
        (fun x => ∑ i, coefficient i * (cutoff x * atom i x)) y := by
    rw [restrictedComplexChartDensity_sum q region 1 hinj]
    simp only [htwist, mul_assoc]
  rw [heq]
  by_cases hy : y ∈ q '' region
  · obtain ⟨x, hx, rfl⟩ := hy
    simp only [restrictedComplexChartDensity_apply q region 1 _ hinj hx,
      Complex.ofReal_one, one_mul]
    exact forecast_single_cutoff_error (source x) (cutoff x) coefficient (fun i => atom i x)
      hε (hcutoff x hx) (hkeep x hx) (herror x hx)
  · rw [restrictedComplexChartDensity_zero q region 1 _ hy,
      restrictedComplexChartDensity_zero q region 1 _ hy, sub_self, norm_zero]
    exact hε

theorem forecast_buffered_twist_coefficient_mass {T : Type*} [Fintype T]
    (coefficient scale : T → ℂ) {M H : ℝ} (hH : 0 ≤ H)
    (hmass : (∑ i, ‖coefficient i‖) ≤ M) (hscale : ∀ i, ‖scale i‖ ≤ H) :
    (∑ i, ‖coefficient i * scale i‖) ≤ M * H := by
  calc
    _ = ∑ i, ‖coefficient i‖ * ‖scale i‖ := by simp only [norm_mul]
    _ ≤ ∑ i, ‖coefficient i‖ * H := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hscale i) (norm_nonneg _))
    _ = (∑ i, ‖coefficient i‖) * H := (Finset.sum_mul _ _ _).symm
    _ ≤ M * H := mul_le_mul_of_nonneg_right hmass hH

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem forecastPhysicalBufferedError
    {U V T : Type*} [Fintype T]
    (target : U → ℂ) (coefficient : T → ℂ) (atom : T → U → V → ℂ)
    (cutoff : U → ℝ) (W : T → U → ℂ) (Good : U → V → Prop)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrange : ∀ u, 0 ≤ cutoff u ∧ cutoff u ≤ 1)
    (hrepresent : ∀ u, cutoff u ≠ 0 → ∃ w, Good u w)
    (hidentity : ∀ t u w, Good u w → (cutoff u : ℂ) * atom t u w = 2 * W t u)
    (hzero : ∀ t u, cutoff u = 0 → W t u = 0)
    (hkeep : ∀ u, target u ≠ 0 → cutoff u = 1)
    (herror : ∀ u w, Good u w → ‖target u - ∑ t, coefficient t * atom t u w‖ ≤ ε) :
    ∀ u, ‖target u - ∑ t, (2 * coefficient t) * W t u‖ ≤ ε := by
  intro u
  by_cases hc : cutoff u = 0
  · have ht : target u = 0 := by
      by_contra hn
      have hk := hkeep u hn
      rw [hc] at hk
      exact zero_ne_one hk
    simpa only [ht, hzero _ _ hc, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
      using hε
  · obtain ⟨w, hw⟩ := hrepresent u hc
    have hbound : ‖(cutoff u : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrange u).1]
      exact (hrange u).2
    have he := forecast_single_cutoff_error (target u) (cutoff u : ℂ)
      coefficient (fun t => atom t u w) hε hbound
      (fun ht => by rw [hkeep u ht, Complex.ofReal_one]) (fun _ => herror u w hw)
    have hsum : (∑ t, coefficient t * ((cutoff u : ℂ) * atom t u w)) =
        ∑ t, (2 * coefficient t) * W t u := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hidentity t u w hw]
      ring
    rwa [hsum] at he

theorem forecastPhysicalBufferedCoefficientMass
    {T : Type*} [Fintype T] (coefficient : T → ℂ) {mass : ℝ}
    (hmass : (∑ t, ‖coefficient t‖) ≤ mass) :
    (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass := by
  calc
    _ = ∑ t, 2 * ‖coefficient t‖ := by norm_num [norm_mul]
    _ = 2 * ∑ t, ‖coefficient t‖ := (Finset.mul_sum ..).symm
    _ ≤ 2 * mass := mul_le_mul_of_nonneg_left hmass (by norm_num)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedTwist
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (coverDegree : ℕ) [NeZero coverDegree] (hcover : M ∣ coverDegree)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let Lg := max ((Lfactor * max 1 Lcoord) * max 1 (M : ℝ≥0)) (4 * M)
    let Lout := Lcut * M + Lg
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ,
      (∀ a, ‖mask a‖ = 1) ∧ (∀ a v, ‖F a v‖ ≤ 1) ∧
      (∀ a, LipschitzWith Lfactor (F a)) ∧
      (∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (density
          ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
            forecastNormalizedActiveCoordinates short
              (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
          star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
            (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
          siteFamilyFactor e k site
            (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
              basisAxisScale (basis (selected a).1) (selected a).2) =
        (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
          F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
            (fun i => (deck j i : ZMod M)))
            (fun i => (u i : ℝ) / physicalN i, allocatedFullMixedSiteValue (R := R) U basis w)) ∧
      ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
        twist.modulus = M ∧ twist.cover = M ∧
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
          (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
            forecastBufferedCoveredSiteFactor B U basis S o hb bW
              coverDegree bufferRadius hbuffer M F (fun i => (u i : ℝ) / physicalN i)
              (physicalSingleSiteValue U coverDegree poly hpoly (fun i => (u i : ℝ))) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u := by
  intro Lspatial Lfactor Lcoord Lcut Lg Lout
  obtain ⟨mask, Fraw, hmask, hFraw, hFrawL, hvalue⟩ :=
    exists_forecastDensityResidueFactor (X := X)
      B U basis hR S density cap lip hbound hLips selected hR1 χ M hM e he k site hd
  let coordinateMap := fun v : (X → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    (forecastNormalizedSpatialCoordinates base physicalN τ v.1, v.2)
  have hcoord : LipschitzWith Lspatial coordinateMap := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change max (dist (forecastNormalizedSpatialCoordinates base physicalN τ v.1)
      (forecastNormalizedSpatialCoordinates base physicalN τ w.1)) (dist v.2 w.2) ≤ _
    have hleft : 8 / τ ≤ (Lspatial : ℝ) := le_max_left _ _
    have hright : (1 : ℝ) ≤ (Lspatial : ℝ) := le_max_right _ _
    apply max_le
    · have h := (forecastNormalizedSpatialCoordinates_lipschitz base physicalN hτ).dist_le_mul v.1 w.1
      change _ ≤ (8 / τ) * dist v.1 w.1 at h
      exact h.trans (mul_le_mul hleft (le_max_left _ _) dist_nonneg (NNReal.coe_nonneg _))
    · calc
        dist v.2 w.2 ≤ dist v w := le_max_right _ _
        _ = 1 * dist v w := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hright dist_nonneg
  let F := fun label => Fraw label ∘ coordinateMap
  have hFL (label) : LipschitzWith Lfactor (F label) := (hFrawL label).comp hcoord
  have hF (label) (v) : ‖F label v‖ ≤ 1 := hFraw label _
  obtain ⟨twist, hmodulus, htwistcover, htwist⟩ :=
    exists_forecast_buffered_normalized_twist B U basis S o hb bW
      coverDegree bufferRadius hbuffer M hcover hR Cinv hCinv hchart hbudget
      Cforward hforward K hK (fun a => star (mask a))
      (fun a => by rw [norm_star, hmask]) F hFL hF
  refine ⟨mask, F, hmask, hF, hFL, ?_, twist, hmodulus, htwistcover, ?_⟩
  · intro u deck w
    have hsp : forecastNormalizedSpatialCoordinates base physicalN τ
        (fun i => (u i : ℝ) / physicalN i) =
        fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8) := by
      funext a
      exact forecastNormalizedSpatialCoordinates_eval base u physicalN τ a
    dsimp only [F, Function.comp_def, coordinateMap]
    rw [hsp]
    exact hvalue u deck w _
  · intro poly hpoly u
    rw [mul_assoc, htwist physicalN poly hpoly u]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedPhysicalAtom
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let Lg := max ((Lfactor * max 1 Lcoord) * max 1 (M : ℝ≥0)) (4 * M)
    let Lout := Lcut * M + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
      twist.modulus = M ∧ twist.cover = M ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ),
        (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
            physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
          (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) *
          ((density
            ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
              forecastNormalizedActiveCoordinates short
                (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2)) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u) ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 0 →
        twist.eval physicalN poly u = 0) := by
  intro Lspatial Lfactor Lcoord Lcut Lg Lout
  obtain ⟨mask, F, _, _, _, hvalue, twist, hmodulus, hcover, htwist⟩ :=
    exists_forecastDensityBufferedTwist (X := X)
      B U basis hR S density cap lip hbound hLips selected hR1 χ M hM e he k site hd base physicalN τ hτ
      o bW hb Cforward hforward K hK M (dvd_refl M)
      bufferRadius hbuffer Cinv hCinv hchart hbudget
  have hcut (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
      (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
        (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) =
      allocatedBufferedSiteChartFactor B U basis S o hb bW M bufferRadius hbuffer
        (fun _ => 1) (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) := by
    simpa only [physicalSingleSiteValue_ambient] using
      allocatedBufferedTorusCutoff_eq_siteChart U basis o bufferRadius hbuffer
        hR Cinv hCinv hchart hbudget B S hb bW M
        (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ)))
  refine ⟨twist, hmodulus, hcover, ?_, ?_⟩
  · intro poly hpoly u w deck hdeck hquarter
    have hy : (fun j (_ : Unit) => QuotientAddGroup.mk ((M : ℝ)⁻¹ •
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)) =
        physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ)) := by
      funext j t
      cases t
      exact (physicalSingleSiteValue_eq_mk U poly hpoly M _ j).symm
    have hbuf := forecastBufferedCoveredSiteFactor_integer_deck
      B U basis S o hb bW M bufferRadius hbuffer F
      (fun i => (u i : ℝ) / physicalN i) w deck
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ))) hdeck hquarter
    dsimp only at hbuf
    rw [hy, ← hcut poly hpoly u] at hbuf
    rw [hvalue u deck w]
    calc
      _ = (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
          forecastBufferedCoveredSiteFactor B U basis S o hb bW M bufferRadius hbuffer M F
            (fun i => (u i : ℝ) / physicalN i)
            (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) := by
        rw [hbuf]
        ring
      _ = _ := htwist poly hpoly u
  · intro poly hpoly u hzero
    have hsite : allocatedBufferedSiteChartFactor B U basis S o hb bW M bufferRadius hbuffer
        (fun _ => 1) (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) = 0 := by
      rw [← hcut poly hpoly u, hzero, Complex.ofReal_zero]
    have hbuf := forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero
      B U basis S o hb bW M bufferRadius hbuffer M F
      (fun i => (u i : ℝ) / physicalN i)
      (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) hsite
    have ht := htwist poly hpoly u
    rw [hbuf, mul_zero] at ht
    have hH : (2 * (((cap : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (2 : ℝ) * ((cap : ℝ) + 1) ≠ 0 by positivity)
    exact (mul_eq_zero.mp ht.symm).resolve_left hH

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

noncomputable def forecastDensityNormalizedAtom
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
    (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  ((density
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short
        (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
    star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
    siteFamilyFactor e k site
      (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
      (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
        basisAxisScale (basis (selected a).1) (selected a).2)) /
    (((cap : ℝ) + 1 : ℝ) : ℂ)

include hR hbound hLips in
theorem exists_forecastDensityBufferedNativeExpansion
    {A Site Term : Type*} [Fintype A] [Fintype Term]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : Term → AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : Term → A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Term → A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ t a, (e t a).Bounds (Tsite t a) (Dsite t a) (Csite t a) Lsite (Hsite t a))
    (k : ∀ t a, (e t a).Term) (site : Site)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let period := fun t => orderOf (χ t) * commonSitePeriod (e t) (k t)
    ∀ {P : ℝ}, 0 ≤ P →
      (∀ t, (period t : ℝ) ≤ Real.exp P) →
      (Lfactor : ℝ) ≤ Real.exp P → (Lcoord : ℝ) ≤ Real.exp P →
      (Lcut : ℝ) ≤ Real.exp P →
    ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      (∀ t, (twists t).modulus = period t ∧ (twists t).cover = period t) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hpoly : ∀ j v, coefficients (poly j) v ∈ U j)
        (coefficient : Term → ℂ) (target : (X → ℤ) → ℂ) (mass ε : ℝ),
        (∑ t, ‖coefficient t‖) ≤ mass → 0 ≤ ε →
        (∀ u, target u ≠ 0 → allocatedBufferedTorusCutoff (R := R) U basis o
          bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1) →
        (∀ (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
          (deck : ∀ j, Eout j → ℤ),
          (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
            (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
              physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
          (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
            (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
          ‖target u - ∑ t, coefficient t *
            forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site
              base physicalN τ u deck w‖ ≤ ε) →
        (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass ∧
        ∀ u, ‖target u - ∑ t, ((2 : ℂ) * coefficient t) *
          (twists t).eval physicalN poly u‖ ≤ ε := by
  intro Lspatial Lfactor Lcoord Lcut period P hP hperiod hfactor hcoord hcut
  have hone (t : Term) : ∃ twist : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      twist.modulus = period t ∧ twist.cover = period t ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ),
        (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
            physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
          (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) *
          forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site
            base physicalN τ u deck w = 2 * twist.eval physicalN poly u) ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 0 →
        twist.eval physicalN poly u = 0) := by
    have hpos : 0 < period t := Nat.mul_pos (zmod_character_order_pos (χ t))
      (commonSitePeriod_pos (e t) (he t) (k t))
    let _ : NeZero (period t) := ⟨hpos.ne'⟩
    obtain ⟨twist, hmod, hcover, hvalue, hzero⟩ :=
      exists_forecastDensityBufferedPhysicalAtom (X := X)
        B U basis hR S density cap lip hbound hLips selected hR1 (χ t) (period t) (dvd_mul_right _ _)
        (e t) (he t) (k t) site
        (fun a => (commonSitePeriod_dvd (e t) (k t) a).trans (dvd_mul_left _ _))
        base physicalN τ hτ o bW hb Cforward hforward K hK
        bufferRadius hbuffer Cinv hCinv hchart hbudget
    have hp' : (period t : ℝ) ≤ Real.exp (3 * P + 3) :=
      (hperiod t).trans (Real.exp_le_exp.mpr (by linarith))
    have hLip := forecastBufferedTwist_lipschitz_exp_bound hP
      (period t) Lfactor Lcoord Lcut (hperiod t) hfactor hcoord hcut
    let result : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩ :=
      twist.mono hp' hp' (show _ ≤ (⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩ : ℝ≥0)
        from hLip)
    refine ⟨result, hmod, hcover, ?_, hzero⟩
    intro poly hpoly u w deck hdeck hquarter
    have h := hvalue poly hpoly u w deck hdeck hquarter
    have hH : ((((cap : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (cap : ℝ) + 1 ≠ 0 by positivity)
    unfold forecastDensityNormalizedAtom
    rw [← mul_div_assoc, h]
    dsimp only [result, NormalizedPolynomialTwist.eval_mono]
    field_simp
    rfl
  choose twists hmod hcover hvalue hzero using hone
  refine ⟨twists, fun t => ⟨hmod t, hcover t⟩, ?_⟩
  intro poly hpoly coefficient target mass ε hmass hε hkeep herror
  refine ⟨forecastPhysicalBufferedCoefficientMass coefficient hmass, ?_⟩
  let cutoff := fun u : X → ℤ => allocatedBufferedTorusCutoff (R := R) U basis o
    bufferRadius hbuffer
    (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle))
  let Good := fun (u : X → ℤ)
      (v : (∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) × (∀ j, Eout j → ℤ)) =>
    (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (v.1 j)) + ((bW j).equivFun.symm (v.2 j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) ∧
    (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (v.1 j)) i| ≤ 1 / 4)
  apply forecastPhysicalBufferedError target coefficient
    (fun t u v => forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site base physicalN τ u v.2 v.1)
    cutoff (fun t u => (twists t).eval physicalN poly u) Good hε
  · intro u
    exact allocatedBufferedTorusCutoff_range U basis o bufferRadius hbuffer hR
      Cinv hCinv hchart hbudget _
  · intro u hu
    obtain ⟨w, deck, hd, hq⟩ := exists_forecast_physical_quarter_recovery B U basis S o hb bW
      bufferRadius hbuffer hR Cinv hCinv hchart hbudget poly hpoly
      (fun i => (u i : ℝ)) hu
    exact ⟨(w, deck), hd, hq⟩
  · intro t u v hv
    exact hvalue t poly hpoly u v.1 v.2 hv.1 hv.2
  · intro t u hu
    exact hzero t poly hpoly u hu
  · exact hkeep
  · intro u v hv
    exact herror u v.1 v.2 hv.1 hv.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

private theorem forecast_density_physical_atom_reassociate (d c f h : ℂ) :
    d * c * f / h = (c * (d / h)) * f := by ring

theorem forecastDensityPhysicalApproximation
    {Term Site : Type*} [Fintype Term]
    (χ : Term → AddChar (Out → ZMod N) ℂ)
    (e : Term → A → ScalarSiteExpansion Site) (k : ∀ t a, (e t a).Term) (site : Site)
    (coefficient : Term → ℂ) (cap : ℝ≥0) {ε : ℝ}
    (herror : ∀ (z : A → ℤ) (out : Out → ZMod N)
        (y : ((Spatial → ℝ) × (Active → ℝ))),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N volume (fun a _ => z a) out : ℂ) -
        ∑ t, coefficient t * ((star (χ t out) * ((density y : ℂ) /
          (((cap : ℝ) + 1 : ℝ) : ℂ))) *
          siteFamilyFactor (e t) (k t) site
            (fun a => (z a : ZMod ((e t a).period (k t a))))
            (fun a => (z a : ℝ) / basisAxisScale (basis (selected a).1) (selected a).2))‖ ≤ ε)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    ‖forecastDensityPhysicalTarget B U basis S density selected sample x active Y N volume
        base physicalN τ o hb bW poly hpoly u -
      ∑ t, coefficient t * forecastDensityNormalizedAtom B U basis S density cap selected
        (χ t) (e t) (k t) site base physicalN τ u deck w‖ ≤ ε := by
  rw [forecastDensityPhysicalTarget_integer_deck B U basis S density selected sample x active Y
    N volume base physicalN τ o hb bW poly hpoly u w deck hdeck hquarter]
  have h := herror (fun a => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N))
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w))
  simpa only [forecastDensityPhysicalDeckSource, forecastDensityNormalizedAtom,
    forecast_density_physical_atom_reassociate] using h

end Erdos3.VectorPolynomial

end

end OAI
