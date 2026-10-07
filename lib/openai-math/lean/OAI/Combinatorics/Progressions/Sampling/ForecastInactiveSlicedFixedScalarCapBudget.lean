import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (Hchild : ℕ)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq in
theorem exists_forecastInactive_sliced_fixed_zero_axis_budgeted_site
    (c0 : ℤ) (hc0 : (constantLaw) c0 ≠ 0)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree)
    {δ : ℝ} (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ}
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let R0 := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) * R j
    let K := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    ∀ {p E : ℝ}, 0 ≤ p → 0 ≤ E → P ≤ Real.exp p → V ≤ Real.exp p →
      (K : ℝ) ≤ Real.exp p → R0 + 1 / 4 ≤ Real.exp p → ε⁻¹ ≤ Real.exp E →
    let O := siteExponentialOutputLog 1 (slicedGridSiteLog j.val 1 degree degree 1 p E)
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (R0 + 1 / 4) ∧
      ∀ (z : ℤ),
        ‖(((height : ℝ) *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
            (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval height (fun _ => z)‖ ≤ 2 * ε := by
  intro V R0 K p E hp hE hPp hVp hKp hRp hεE O
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨hQ, hRQ, _, hεQ, _, hLQ, hKQ, hKLQ, herror, hsize, hperiod, hcap⟩ :=
    slicedGridSite_numerics 0 j.val 1 degree degree K (by norm_num : (0 : ℝ) ≤ 1)
      hp hE (by norm_num) (by norm_num) hP hV hV hV hV
      hPp hVp hVp hVp hVp hKp hRp hε hε1 hεE
  simp only [pow_one, Nat.cast_one, one_mul, pow_zero, mul_one] at hKQ hKLQ hLQ
  obtain ⟨e, he, herr⟩ := exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i Hchild c0 hc0 hgrid
    hsmall hδ hreg A hA P hP hsP hstride hB hε hε1 hσ1
    hQ hRQ hεQ hLQ hKQ hKLQ herror
  have hsize' := (le_max_right _ _).trans ((le_max_right _ _).trans hsize)
  have hperiod' := (le_max_right _ _).trans ((le_max_right _ _).trans hperiod)
  have hcap' := (le_max_right _ _).trans ((le_max_right _ _).trans hcap)
  obtain ⟨hT, hper, hC, hL, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ hsize' hperiod' hcap'
  have h1 := Real.one_le_exp_iff.mpr hQ
  obtain ⟨hT1, hper1, hC1, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1
  simp only [Nat.cast_one, one_mul] at hT hC hT1 hC1
  refine ⟨e, he.mono (max_le hT hT1) (max_le hper hper1) (max_le hC hC1) ?_ le_rfl, herr⟩
  exact_mod_cast hL

def slicedFixedZeroGeometryLog {A : Type*} [Semiring A]
    (D v w vq vchild : A) : A :=
  slicedGridGeometryLog D v w (vq + w + 1) +
    (2 * (D + v + 8) + D * (vchild + 1) + 4)

theorem slicedFixedZeroGeometryLog_nonneg {D v w vq vchild : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild) :
    0 ≤ slicedFixedZeroGeometryLog D v w vq vchild := by
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  positivity

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    {δ D v w vq vchild : ℝ}
    (hD : 1 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hδ : 0 < δ) (hRj : 0 < R j)
    (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hqv : (q : ℝ) ≤ Real.exp vq)
    (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v) :
    let p := slicedFixedZeroGeometryLog D v w vq vchild
    ((torus : ℝ) * cost / δ ^ degree ≤ Real.exp p) ∧
    ((max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom) : ℕ) : ℝ) ≤ Real.exp p ∧
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
      R j + 1 / 4 ≤ Real.exp p := by
  intro p
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let T : ℕ := Nat.ceil ((q : ℝ) / δ)
  let p0 := slicedGridGeometryLog D v w (vq + w + 1)
  let g := D + v + 8
  let pf := 2 * g + D * (vchild + 1) + 4
  have hp0 : 0 ≤ p0 := by dsimp [p0, slicedGridGeometryLog]; positivity
  have hpf : 0 ≤ pf := by dsimp [pf, g]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hp0p : p0 ≤ p := by change p0 ≤ p0 + pf; linarith
  have hpfp : pf ≤ p := by change pf ≤ p0 + pf; linarith
  have hfrac : (q : ℝ) / δ ≤ Real.exp (vq + w) := by
    rw [div_eq_mul_inv]
    exact (mul_le_mul hqv hδw (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  have hT : (T : ℝ) ≤ Real.exp (vq + w + 1) :=
    natCeil_le_exp_succ (by positivity) (by positivity) hfrac
  obtain ⟨_, hV, _, _, hK, hsupport⟩ := allocatedSlicedGrid_geometry_bounds
    B R j i 0 1 T hD0 hv hw (by positivity) hδ hRj (by simpa using hD0) hdegree (by simpa using hD) htail hb
    hRv hRi hδw hT hcoeff
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hγinv := (principalProfileSize_exp_bounds _ hRj hslots hRv hRi).2
  have hden := inactiveDenominator_le_exp (principalProfileSize_pos hRj _) hg hγinv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ degree ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) degree hdegree
  have hpchild := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg Hchild) hchild hvc degree hdegree
  have hfirst : (denom : ℝ) * 2 ^ degree * (Hchild : ℝ) ^ degree ≤
      Real.exp (g + 1 + D + D * vchild) := by
    have h := mul_le_mul (mul_le_mul hden hp2 (by positivity) (Real.exp_nonneg _))
      hpchild (by positivity) (by positivity)
    simpa only [← Real.exp_add] using h
  have hlast : (2 : ℝ) * denom ≤ Real.exp (g + 2) := by
    have h := mul_le_mul htwo hden (Nat.cast_nonneg _) (Real.exp_nonneg _)
    exact h.trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  have hfixed : ((denom * 2 ^ degree * Hchild ^ degree + 2 * denom : ℕ) : ℝ) ≤ Real.exp pf := by
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hfirst hlast
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact hsum.trans_eq (by congr 1; dsimp [pf]; ring)
  refine ⟨hV.trans (Real.exp_le_exp.mpr hp0p), ?_, ?_⟩
  · rw [Nat.cast_max]
    exact max_le (hK.trans (Real.exp_le_exp.mpr hp0p)) (hfixed.trans (Real.exp_le_exp.mpr hpfp))
  · simp only [Nat.cast_zero, pow_zero, zero_add, one_pow, one_mul, mul_one, Nat.cast_one] at hsupport
    exact hsupport.trans (Real.exp_le_exp.mpr hp0p)

include hq in
theorem exists_forecastInactive_sliced_fixed_zero_axis_primitive_budgeted_site
    {D v w vq vchild p E : ℝ}
    (c0 : ℤ) (hc0 : (constantLaw) c0 ≠ 0)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree)
    {δ : ℝ} (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ}
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1)
    (hD : 1 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hPp : P ≤ Real.exp p) (hεE : ε⁻¹ ≤ Real.exp E)
    (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hqv : (q : ℝ) ≤ Real.exp vq)
    (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v) :
    let pAll := p + slicedFixedZeroGeometryLog D v w vq vchild
    let O := siteExponentialOutputLog 1 (slicedGridSiteLog j.val 1 degree degree 1 pAll E)
    let R0 := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) * R j
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (R0 + 1 / 4) ∧
      ∀ (z : ℤ),
        ‖(((height : ℝ) *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
            (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval height (fun _ => z)‖ ≤ 2 * ε := by
  intro pAll O R0
  obtain ⟨hV, hK, hRadius⟩ := forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    (B := B) (R := R) (j := j) (i := i) (q := q) (Hchild := Hchild)
    hD hv hw hvq hvc hδ (hR j) hdegree htail hb hRv hRi hδw hqv hchild hcoeff
  have hg := slicedFixedZeroGeometryLog_nonneg (zero_le_one.trans hD) hv hw hvq hvc
  have hpAll : 0 ≤ pAll := add_nonneg hp hg
  have hpLe : p ≤ pAll := le_add_of_nonneg_right hg
  have hgLe : slicedFixedZeroGeometryLog D v w vq vchild ≤ pAll := le_add_of_nonneg_left hp
  exact exists_forecastInactive_sliced_fixed_zero_axis_budgeted_site
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i Hchild c0 hc0 hgrid
    hsmall hδ hreg A hA P hP hsP hstride hB hε hε1 hσ1 hpAll hE
    (hPp.trans (Real.exp_le_exp.mpr hpLe))
    (hV.trans (Real.exp_le_exp.mpr hgLe)) (hK.trans (Real.exp_le_exp.mpr hgLe))
    (hRadius.trans (Real.exp_le_exp.mpr hgLe)) hεE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq in
theorem forecastInactive_sliced_fixed_zero_axis_norm_le_primitive_budget
    (δ P : ℝ) (Hchild : ℕ)
    (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (hsmall : height ≤ S.value ^ degree)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {D v w vq vchild p : ℝ}
    (hD : 1 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hqv : (q : ℝ) ≤ Real.exp vq)
    (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (c0 z : ℤ) :
    let pAll := p + slicedFixedZeroGeometryLog D v w vq vchild
    ‖(((height : ℝ) *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
        (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (slicedGridSiteLog j.val 1 degree degree 1 pAll 0) := by
  intro pAll
  let V := (torus : ℝ) * cost / δ ^ degree
  let K := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
    (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
  obtain ⟨hV, hK, _⟩ := forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    (B := B) (R := R) (j := j) (i := i) (q := q) (Hchild := Hchild)
    hD hv hw hvq hvc hδ (hR j) hdegree htail hb hRv hRi hδw hqv hchild hcoeff
  have hg := slicedFixedZeroGeometryLog_nonneg (zero_le_one.trans hD) hv hw hvq hvc
  have hpAll : 0 ≤ pAll := add_nonneg hp hg
  have hpLe : p ≤ pAll := le_add_of_nonneg_right hg
  have hgLe : slicedFixedZeroGeometryLog D v w vq vchild ≤ pAll := le_add_of_nonneg_left hp
  have hVP : V ≤ Real.exp pAll := hV.trans (Real.exp_le_exp.mpr hgLe)
  have hKP : (K : ℝ) ≤ Real.exp pAll := hK.trans (Real.exp_le_exp.mpr hgLe)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hbudget := slicedGridPointCap_exp_bound 0 j.val 1 degree degree K
    (by norm_num : (0 : ℝ) ≤ 1) hpAll (by norm_num) (by norm_num)
    hP hV0 hV0 hV0 hV0 (hPp.trans (Real.exp_le_exp.mpr hpLe)) hVP hVP hVP hVP hKP
  simp only [pow_one] at hbudget
  have hkb := (le_max_left _ _).trans ((le_max_right _ _).trans hbudget)
  have hcb := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hbudget))
  exact (forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i δ P Hchild hδ hreg hsmall hgrid
    A hA hP hsP hstride hB c0 z).trans (max_le hkb hcb)

end Erdos3.VectorPolynomial

end

end OAI
