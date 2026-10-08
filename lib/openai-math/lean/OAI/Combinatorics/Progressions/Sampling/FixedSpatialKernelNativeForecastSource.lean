/-
Modified for ProveIt: unfold local definitions when rewriting retained
forecast expansions into their error estimates on Lean 4.32. All upstream
statements and quantitative bounds are unchanged.
-/
import OAI.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
import OAI.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_retained_character_sites
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (poly : Out → MvPolynomial (V ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (V → ZMod N))
    (T : ℕ) (_hT : 0 < T)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hTv : (T : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : T ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {Pscale : ℝ} (hPscale : 0 ≤ Pscale)
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ)
          (fun r => (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
            forecastInactiveCharacterCoefficient poly N pRat χ.val r.val) t‖)
        ≤ (T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(∑ χ : Ch, ((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ.val *
            (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) * star (χ.val outPoint)) -
          (∑ χ : Ch, (∑ r : Pos χ, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
            forecastInactiveCharacterCoefficient poly N pRat χ.val r.val *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a)) *
              star (χ.val outPoint))‖ ≤ (T : ℝ) ^ (Fintype.card Out + 1) * δ := by
  intro law Ch Pos scale W O
  have horder (χ : Ch) : orderOf χ.val ≤ T := (Finset.mem_filter.mp χ.property).2
  have heach (χ : Ch) := exists_forecastInactive_character_physical_site B U b S hR hσ
    selected hselected poly N pRat χ.val hD hP hp hv hPp
    ((Nat.cast_le.mpr (horder χ)).trans hTv) hδ hE hδE
    ((horder χ).trans hsize) hR1 hsmall hgrid c hc hσ1 L hL
    ((scalarCubePrimitiveEnvelope_mono Empty L (le_refl (1 : ℝ≥0))
      (le_refl (0 : ℝ≥0)) (horder χ)).trans hprimitive)
    hB hPscale hRinv hslots
  choose e he hmass herr using heach
  have hcard : (Fintype.card Ch : ℝ) ≤ (T : ℝ) ^ (Fintype.card Out + 1) := by
    have hb := finiteCharacter_boundedOrder_card_le (integerResidueTuple (J := Out) N)
      (integerResidueTuple_surjective N) T
    have hnat : Fintype.card Ch ≤ T ^ (Fintype.card Out + 1) := by
      simpa only [Fintype.card_coe] using hb
    exact_mod_cast hnat
  refine ⟨e, he, ?_, ?_⟩
  · calc
      _ ≤ ∑ _χ : Ch, Real.exp (Fintype.card A * O) :=
        Finset.sum_le_sum (fun χ _ => hmass χ)
      _ = (Fintype.card Ch : ℝ) * Real.exp (Fintype.card A * O) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
  · intro x z outPoint
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ χ : Ch, ‖((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ.val *
            (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) * star (χ.val outPoint) -
          (∑ r : Pos χ, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
            forecastInactiveCharacterCoefficient poly N pRat χ.val r.val *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a)) *
              star (χ.val outPoint)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : Ch, δ := by
        apply Finset.sum_le_sum
        intro χ _
        rw [← sub_mul, norm_mul, norm_star, AddChar.norm_apply, mul_one]
        exact herr χ x z
      _ = (Fintype.card Ch : ℝ) * δ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδ.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecast_rational_site_approximation
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (poly : Out → MvPolynomial (V ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (V → ZMod N))
    (T : ℕ) (hT : 0 < T)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hTv : (T : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : T ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {Pscale : ℝ} (hPscale : 0 ≤ Pscale)
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay)) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ)
          (fun r => (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
            forecastInactiveCharacterCoefficient poly N pRat χ.val r.val) t‖)
        ≤ (T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected c x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          (∑ χ : Ch, (∑ r : Pos χ, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
            forecastInactiveCharacterCoefficient poly N pRat χ.val r.val *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a)) *
              star (χ.val outPoint))‖ ≤
          (∏ a, (scale a : ℝ)) * law.fiberMean (forecastInactiveFixedOutput B U b S selected c x)
            (fun a _ => z a) (fun _ => 1) * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δ := by
  intro law Ch Pos scale W O
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_retained_character_sites B U b S hR hσ
    selected hselected poly N pRat T hT hD hP hp hv hPp hTv hδ hE hδE
    hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
  refine ⟨e, he, hmass, ?_⟩
  intro x z outPoint
  apply rationalInactiveForecast_retained_approximation law (fun _ => pRat)
    (forecastInactiveFixedOutput B U b S selected c x)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (show 0 ≤ ∏ a, (scale a : ℝ) from
      Finset.prod_nonneg (fun a _ => Nat.cast_nonneg (scale a))) hCdecay hPdecay hdecay
    T hT (fun a _ => z a) outPoint _
  simpa only [Complex.ofReal_prod, Complex.ofReal_natCast] using herr x z outPoint

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (poly : Out → MvPolynomial (V ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)

variable (N : ℕ)

variable [siteInst2 : NeZero N]

variable (pRat : FiniteProbabilityWeights (V → ZMod N))

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)

variable (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)

variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

variable {Cdecay Pdecay : ℝ}

variable (hCdecay : 0 ≤ Cdecay)

variable (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)

variable (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))

include selected hselected siteInst1 poly N siteInst2 pRat T hT hD hP hp hv hPp hTv hδ hE hδE hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots hCdecay hPdecay hdecay

theorem exists_forecast_actual_smooth_rational_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
    (Pg : LayerSamplerAxis I n → Prop) [DecidablePred Pg]
    (site : Empty ↪ Zsp) (root : Zsp → ℤ) (dirs : Matrix Empty Zsp ℤ)
    (hpivot : (selectedSpatialPivot root dirs site).det ≠ 0)
    {Wsp Lsp : ℝ} (hWsp : 0 ≤ Wsp) (hLsp : 0 < Lsp)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬Pg a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬Pg a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {amin δslice : ℝ} (hamin : 0 < amin) (hδslice : 0 < δslice)
    (hprincipal : ∀ a : {a : LayerSamplerAxis I n // ¬Pg a},
      amin ≤ unitProfilePrincipalSize (B := B) a.val)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (ractive : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) Pg → ℝ)
    (hractive : ∀ e, |ractive e| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wsp)
    (hminor : κ ≤ |(Matrix.of (fun i j => (dirs i (site j) : ℝ) / Lsp)).det|) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let SmoothCoord := (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬Pg a}, Unit) → ℝ))
    let density := allocatedFixedPathForecastDensity (X := X)
      B Pg R σ site root dirs hpivot hWsp hLsp hBactive lower width ractive
    let Cs := (Real.toNNReal (anisotropicSpatialDensityCap site κ) + 1) ^ Fintype.card X
    let Ks := Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip site κ) *
      (Real.toNNReal (anisotropicSpatialDensityCap site κ) + 1) ^ Fintype.card X
    let Acap := allocatedFixedPathLiftRowCap Pg hamin hδslice
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (H : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith
        (Cl * Ks + Cs * Kl + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected c x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  intro law Ch Pos scale W O SmoothCoord density Cs Ks Acap Cl Kl H Ig weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hmass, herr⟩ := exists_forecast_rational_site_approximation B U b S hR hσ
    selected hselected poly N pRat T hT hD hP hp hv hPp hTv hδ hE hδE
    hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
    hCdecay hPdecay hdecay
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  have hext (outPoint : Out → ZMod N) := forecastRetained_actual_smooth_expansion (X := X)
    B Pg R σ site root dirs hpivot hWsp hLsp (fun j => (hR j).ne') hBactive lower width
    hamin hδslice hprincipal hwidth hlower ractive hractive hκ hroot hminor e he weight
    (fun χ : Ch => star (χ.val outPoint)) (fun χ => by simp only [norm_star, AddChar.norm_apply]; exact le_rfl)
    hmass
  refine ⟨(hext 0).1, (fun b t z => (hext b).2.1 t z),
    (fun b t z => (hext b).2.2.1 t z), ?_⟩
  intro x z outPoint y
  have hcap := forecastInactive_fixed_grid_mass_exp_bound B U b S hR hσ selected hselected
    hD hPcap hpcap hPcapp hR1 hsmall c hc L hL hprimitiveCap hB hRinv hslots x z
  have herror := (herr x z outPoint).trans
    (add_le_add (mul_le_mul_of_nonneg_right hcap
      (div_nonneg hCdecay (Nat.cast_nonneg T))) (le_refl _))
  have hfinal := forecastRetained_actual_smooth_error (X := X)
    B Pg R σ site root dirs hpivot hWsp hLsp (fun j => (hR j).ne') hBactive lower width
    hamin hδslice hprincipal hwidth hlower ractive hractive hκ hroot hminor y herror
  erw [(hext outPoint).2.2.2 z (y, fun a => (z a : ℝ) / scale a)] at hfinal
  exact hfinal

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (poly : Out → MvPolynomial (V ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)

variable (N : ℕ)

variable [siteInst2 : NeZero N]

variable (pRat : FiniteProbabilityWeights (V → ZMod N))

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)

variable (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)

variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

variable {Cdecay Pdecay : ℝ}

variable (hCdecay : 0 ≤ Cdecay)

variable (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)

variable (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))

include selected hselected siteInst1 poly N siteInst2 pRat T hT hD hP hp hv hPp hTv hδ hE hδE hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots hCdecay hPdecay hdecay

theorem exists_forecast_continuous_rational_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hdensity : ∀ y, ‖density y‖ ≤ H)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (H : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith
        (densityLip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected c x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  intro law Ch Pos scale W O Ig weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hmass, herr⟩ := exists_forecast_rational_site_approximation B U b S hR hσ
    selected hselected poly N pRat T hT hD hP hp hv hPp hTv hδ hE hδE
    hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
    hCdecay hPdecay hdecay
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  have hext (outPoint : Out → ZMod N) := forecastRetained_continuous_expansion
    density H hH hdensity densityLip hdensityLip e he weight
    (fun χ : Ch => star (χ.val outPoint)) (fun χ => by simp only [norm_star, AddChar.norm_apply]; exact le_rfl)
    hmass
  refine ⟨(hext 0).1, (fun b t z => (hext b).2.1 t z),
    (fun b t z => (hext b).2.2.1 t z), ?_⟩
  intro x z outPoint y
  have hcap := forecastInactive_fixed_grid_mass_exp_bound B U b S hR hσ selected hselected
    hD hPcap hpcap hPcapp hR1 hsmall c hc L hL hprimitiveCap hB hRinv hslots x z
  have herror := (herr x z outPoint).trans
    (add_le_add (mul_le_mul_of_nonneg_right hcap
      (div_nonneg hCdecay (Nat.cast_nonneg T))) (le_refl _))
  have hfinal := forecastRetained_continuous_error density H hH hdensity y herror
  erw [(hext outPoint).2.2.2 z (y, fun a => (z a : ℝ) / scale a)] at hfinal
  exact hfinal

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (inactive : LayerSamplerAxis I n → Prop)
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  inactive noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables inactive G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables inactive G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout inactive)
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial inactive base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance modularSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)

variable (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)

variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

theorem exists_allocated_modular_forecast_continuous_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hdensity : ∀ y, ‖density y‖ ≤ H)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (H : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith
        (densityLip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected c x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  have hCdecay : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay :=
    allocatedCongruenceForecastRankConstant_dimension inactive hm Dmod hDmod
  have hdecay (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product inactive noise rdeck projection spatial kernel block
      hm Pr Aexp epres hPr Cmod (Nat.cast_nonneg _) Rbad hbad base origin
      (fun k => (y k.1 k.2 : ℤ)) χ
  exact exists_forecast_continuous_rational_source B U b S hR hσ
    selected hselected poly N pRat T hT hD hP hp hv hPp hTv hδ hE hδE
    hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB hPscale hRinv hslots
    hCdecay hPdecay hdecay hPcap hpcap hPcapp hprimitiveCap
    density H hH hdensity densityLip hdensityLip

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance originalSampleSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)

variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))

local notation "pathCoefficients" => allocatedOriginalSampleInactiveCoefficients B selected sample

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall sample hs hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

theorem exists_allocated_original_sample_modular_forecast_continuous_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hdensity : ∀ y, ‖density y‖ ≤ H)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (H : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith
        (densityLip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U b S selected pathCoefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (scale a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / scale a)‖ ≤
          H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  have hc := allocatedOriginalSampleInactiveCoefficients_supported B selected U b hR hσ S sample hs
  have hgrid (a : A) := allocatedShortAxis_grid B U b S
    ⟨(selected a).1, Sum.inr (selected a).2⟩ (hsmall a)
  exact exists_allocated_modular_forecast_continuous_source
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (inactive := (allocatedShortAxis (I := I) U b S.value)) (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres)
    (hPr := hPr) (Dmod := Dmod) (hDmod := hDmod)
    (noise := noise) (rdeck := rdeck) (projection := projection)
    (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    (selected := selected) (hselected := hselected) (T := T) (hT := hT)
    (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
    (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize)
    (hR1 := hR1) (hsmall := hsmall) (hgrid := hgrid) (c := pathCoefficients) (hc := hc)
    (hσ1 := hσ1) (L := L) (hL := hL) (hprimitive := hprimitive) (hB := hB)
    (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
    (hPcap := hPcap) (hpcap := hpcap) (hPcapp := hPcapp) (hprimitiveCap := hprimitiveCap)
    (density := density) (H := H) (hH := hH) (hdensity := hdensity)
    (densityLip := densityLip) (hdensityLip := hdensityLip)

end RationalSite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance nativeForecastSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)

variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))

local notation "pathCoefficients" => allocatedOriginalSampleInactiveCoefficients B selected sample

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall sample hs hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

theorem exists_allocated_density_native_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U b S.value a}, Unit) → ℝ) → ℝ)
    (cap lip : ℝ≥0) (hbound : ∀ y, |density y| ≤ (cap : ℝ))
    (hLips : LipschitzWith lip density)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    let H : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative → v + Fintype.card A * O ≤ Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  intro law Ch Pos scale W O Ig weight H Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  have hH : 1 ≤ H := by dsimp only [H]; linarith [cap.property]
  have hdensity : ∀ y, ‖density y‖ ≤ H := fun y =>
    (show ‖density y‖ ≤ (cap : ℝ) by simpa only [Real.norm_eq_abs] using hbound y).trans (by dsimp only [H]; linarith)
  obtain ⟨e, he, hmass, _, _, herror⟩ :=
    exists_allocated_original_sample_modular_forecast_continuous_source
      (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
      (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
      (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
      (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
      (selected := selected) (hselected := hselected) (T := T) (hT := hT)
      (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
      (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize) (hR1 := hR1) (hsmall := hsmall)
      (sample := sample) (hs := hs) (hσ1 := hσ1) (L := L) (hL := hL)
      (hprimitive := hprimitive) (hB := hB) (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
      hPcap hpcap hPcapp hprimitiveCap density H hH hdensity lip hLips
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
    dsimp only [Pos]
    infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
  have hperiodTerm (t : Term) :
      ((orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 : ℕ) : ℝ) ≤ Real.exp Pnative := by
    have horder : (orderOf t.1.val : ℝ) ≤ Real.exp v :=
      (Nat.cast_le.mpr (Finset.mem_filter.mp t.1.property).2).trans hTv
    have hsite := commonSitePeriod_le_pow (e t.1 t.2.1) (he t.1 t.2.1)
      (fun _ => le_rfl) t.2.2
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp v * (Real.exp O) ^ Fintype.card A :=
        mul_le_mul horder hsite (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (v + Fintype.card A * O) := by conv_rhs => rw [Real.exp_add, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hperiod
  obtain ⟨twists, hmod, htransfer⟩ := exists_forecastDensityBufferedNativeExpansion
    B U b hR S density cap lip hbound hLips selected hR1
    (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
    (fun t a => he t.1 t.2.1 a) (fun t : Term => t.2.2) ∅ base physicalN τ hτ
    o bW hb forward hforward K hK radius hr inverse hinverse hchart hbudget
    hPnative hperiodTerm hfactor hcoord hcut
  refine ⟨e, he, twists, hmod, ?_, ?_⟩
  · simpa only [mul_assoc] using forecastPhysicalBufferedCoefficientMass coeff hmass
  · intro x physicalPoly hphysical
    let target := forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical
    have hε : 0 ≤ H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
      have hdec : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    apply (htransfer physicalPoly hphysical coeff target
      (H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)))
      (H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ))
      hmass hε ?_ ?_).2
    · intro u hu
      exact forecastDensityPhysicalTarget_cutoff_of_active_support
        B U b S density selected sample x (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW
        hR hσ hs hσ1 hexhaustive hactive radius hr hr3 hradius
        inverse hinverse hchart hbudget physicalPoly hphysical u hu
    · intro u w deck hdeck hquarter
      exact forecastDensityPhysicalApproximation B U b S density selected sample x
        (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW
        (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
        (fun t : Term => t.2.2) ∅ coeff cap (herror x)
        physicalPoly hphysical u w deck hdeck hquarter

end RationalSite
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Vact" => LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)
local notation "Pdecay" => modularRankDecayExponent m Cmod
local notation "Cdecay" => (((Rbad * ∏ q : Pr, (Subtype.val q) ^ epres (Subtype.val q) : ℕ) : ℝ) ^
  (modularRankDecayExponent m Cmod * modularRankChargeFactor m))

local instance fixedSpatialNativeForecastSourceModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)

variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))

local notation "pathCoefficients" => allocatedOriginalSampleInactiveCoefficients B selected sample

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall sample hs hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hPr hDmod hbad

variable {Tsp : Type*} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
variable (hdet0 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0)
variable (hdet1 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0)
variable (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
variable {δslice : ℝ} (hδslice : 0 < δslice)
variable (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
variable (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
include hτ hwidth hlower hcontained hdet0 hdet1

theorem exists_fixedSpatialKernel_native_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    let density := fixedSpatialKernelOriginalForecastDensity B U b S
      spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) hdet0 hdet1 hBactive lower width sample
    let cap := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true hdet1) hδslice
    let lip := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) false hdet0)
      (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) true hdet1) hδslice
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    let H : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative → v + Fintype.card A * O ≤ Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastDensityPhysicalTarget B U b S density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  intro density cap lip law Ch Pos instPos scale W O Ig weight H Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  have hG := fixedSpatialKernelOriginalForecastDensity_bounds B U b hR hσ S
    spatialEquiv Wsp Lsp (fun k : Option G × X => (noise (Option.map Sum.inl (Prod.fst k), Prod.snd k) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k) hdet0 hdet1 hBactive lower width
    hδslice hwidth hlower sample hs
  have hGbound (y) : |density y| ≤ (cap : ℝ) := by
    rw [abs_of_nonneg (hG.1 y).1]
    exact (hG.1 y).2
  have hactive (y) (hy : density y ≠ 0) (a) : |y.2 a| ≤ (3 : ℝ) := by
    have hn : ‖y.2‖ ≤ (2 : ℝ) := by
      by_contra hnorm
      have hzero := allocatedFixedPathLiftDensity_zero_off_ball B
        (allocatedShortAxis (I := I) U b S.value) R σ (fun j => (hR j).ne')
        hBactive lower width hcontained (unitProfilePrincipalLowerBound_pos B)
        hδslice (fun a => unitProfilePrincipalLowerBound_le B a.val) hwidth hlower
        (allocatedSampleRestrictedProfileNoise B U b S
          (allocatedShortAxis (I := I) U b S.value) sample)
        (allocatedSampleRestrictedProfileNoise_short_abs_le B U b hR hσ S sample hs)
        y.2 (lt_of_not_ge hnorm)
      apply hy
      simp only [density, fixedSpatialKernelOriginalForecastDensity, binaryDensity, hzero, mul_zero]
    have ha : |y.2 a| ≤ ‖y.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
    linarith
  exact exists_allocated_density_native_forecast_source
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres) (hPr := hPr)
    (Dmod := Dmod) (hDmod := hDmod) (noise := noise) (rdeck := rdeck)
    (projection := projection) (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin)
    (selected := selected) (hselected := hselected) (T := T) (hT := hT)
    (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
    (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize) (hR1 := hR1) (hsmall := hsmall)
    (sample := sample) (hs := hs) (hσ1 := hσ1) (L := L) (hL := hL)
    (hprimitive := hprimitive) (hB := hB) (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
    hPcap hpcap hPcapp hprimitiveCap density cap lip hGbound hG.2 hactive physicalN τ hτ
    o bW hb forward hforward K hK radius hr hr3 hradius inverse hinverse hchart hbudget hexhaustive
    hPnative hperiod hfactor hcoord hcut

end RationalSite
end Erdos3.VectorPolynomial

end

end OAI
