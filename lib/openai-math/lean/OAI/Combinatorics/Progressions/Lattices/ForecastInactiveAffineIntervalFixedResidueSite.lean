import OAI.Combinatorics.Progressions.Sampling.ContainedProgressionForecastDisintegration
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedPath
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedProduct
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedPath

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

noncomputable def forecastInactiveFixedOutput
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :
    A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ := fun a =>
  boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) ((selected a).1.val + 1)
    (fun t : (Finset.univ : Finset (Finset Empty)) => (t : Finset Empty)) *ᵥ c a

theorem exists_forecastInactive_fixed_residue_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (q : ℕ) [NeZero q]
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
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
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
      (selected a).1 (selected a).2
    let O := allocatedInactiveJointSiteLog m D p v E
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e
        (fun r => (law.mass (Finset.univ.filter
          (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val) t‖)
        ≤ Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => coefficient (principalResidueLabel q y) *
            (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) -
          (∑ r : Pos, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val *
            siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a))‖ ≤ δ := by
  intro law Pos scale O
  let c₀ (a : A) := c a (constantCoefficientSlot _ _)
  have hc₀ (a : A) : allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c₀ a) ≠ 0 := by
    exact hc a _
  have heach (r : Pos) := exists_forecastInactive_fixed_product_site B U b S hR hσ
    selected hselected q (NeZero.pos q) r.val hD hP hp hv hPp hqv hδ hE hδE
    hsize hR1 hsmall r.property hgrid c₀ hc₀ hσ1 L hL hprimitive hB
  choose e he herr using heach
  have hmass : (∑ r : Pos, law.mass (Finset.univ.filter
      (fun y => principalResidueLabel q y = r.val))) ≤ 1 :=
    (forecastInactive_positiveResidue_mass_sum law (principalResidueLabel q)).le
  let w (r : Pos) := law.mass (Finset.univ.filter
    (fun y => principalResidueLabel q y = r.val))
  have hw (r : Pos) : 0 ≤ w r := law.mass_nonneg _
  refine ⟨e, he, ?_, ?_⟩
  · have hm := forecastSiteMixture_weighted_mass e he
      (fun _ => Real.exp_nonneg O) w (fun r => coefficient r.val) hw hmass
      (fun r => hcoefficient r.val)
    simpa only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul] using hm
  · intro x z
    let μ (r : Pos) : ℂ := (((∏ a, (scale a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedResidueJetPMF B U b hR hσ S q r.val r.property
        (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a))
        (fun a _ => z a)).toReal : ℝ) : ℂ)
    have herr' := forecastSiteMixture_weighted_error e w (fun r => coefficient r.val) μ
      hw hmass (fun r => hcoefficient r.val) (fun _ => z)
      (fun _ a => (z a : ℝ) / scale a) hδ.le (fun r => herr r z)
    have hdis := forecastInactive_indicator_disintegration law (principalResidueLabel q)
      (forecastInactiveFixedOutput B U b S selected c x) (fun a _ => z a) coefficient
    have hconst (c : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => c) t = c := by
      simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
    have hjoint (r : Pos) :
        (law.condition (Finset.univ.filter (fun y => principalResidueLabel q y = r.val))
          r.property).toPMF.map (forecastInactiveFixedOutput B U b S selected c x) =
        dependentProductPMF (fun a => allocatedSupportedResidueJetPMF B U b hR hσ S q r.val r.property
          (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a)) := by
      have h := forecastInactiveFixedPath_joint_law B U b hR hσ S q r.val r.property
        selected hselected hsmall c hc x (fun _ => (Finset.univ : Finset (Finset Empty)))
      unfold forecastInactiveFixedOutput
      simpa only [hconst, law, c₀] using h
    simp_rw [hjoint] at hdis
    rw [hdis, Finset.mul_sum]
    have heq : (∑ r : Pos, ((∏ a, (scale a : ℝ)) : ℂ) *
        ((w r : ℂ) * coefficient r.val *
          ((dependentProductPMF (fun a => allocatedSupportedResidueJetPMF B U b hR hσ S q r.val r.property
            (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a))
            (fun a _ => z a)).toReal : ℂ))) =
        ∑ r : Pos, (w r : ℂ) * coefficient r.val * μ r := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      push_cast
      ring
    rw [heq]
    exact herr'

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

theorem forecastInactive_sliced_fixed_residue_identity
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (q : ℕ) [NeZero q]
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hH : ∀ t, 0 < H t)
    (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower (allocatedPrincipalSides_pos B U b S) hsubset
    (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a) then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step lower q r.val) *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r.val
            H step lower hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c a (constantCoefficientSlot _ _)))
            (fun a _ => z a)).toReal : ℂ) := by
  intro p map
  rw [containedProgressionForecast_indicator_disintegration]
  apply Finset.sum_congr rfl
  intro r _
  have hj := forecastInactiveSlicedFixedPath_joint_law B U b hR hσ S q r.val
    H step lower hH hsubset r.property selected hselected hsmall c hc x
    (fun _ => (Finset.univ : Finset (Finset Empty)))
  have hconst (v : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => v) t = v := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  simp only [hconst] at hj
  rw [show (containedSupportedProgressionLaw B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower (allocatedPrincipalSides_pos B U b S)
      hH hsubset q r.val r.property).toPMF.map (forecastInactiveFixedOutput B U b S selected c x) = _
    from hj]

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

theorem forecastInactive_affineInterval_fixed_residue_identity
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (q : ℕ) [NeZero q]
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hH : ∀ t, 0 < H t)
    (hinside : ∀ j (t : Fin (H j)),
      0 ≤ lower j + (step j : ℤ) * t.val ∧
        lower j + (step j : ℤ) * t.val < allocatedPrincipalSides B U b S j)
    (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    (principalAffineIntervalLaw B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower hinside hH).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a) then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step lower q r.val) *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r.val
            H step lower hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c a (constantCoefficientSlot _ _)))
            (fun a _ => z a)).toReal : ℂ) := by
  intro p
  rw [principalAffineIntervalLaw_eq_contained B (layerSamplerDegree I n) H hH
    (allocatedPrincipalSides B U b S) step lower (allocatedPrincipalSides_pos B U b S) hinside hsubset]
  exact forecastInactive_sliced_fixed_residue_identity B U b S hR hσ selected hselected
    q H step lower hH hsubset coefficient hsmall c hc x z

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
variable (q : ℕ) [NeZero q]
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_forecastInactive_sliced_fixed_residue_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) →
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) →
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) →
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) →
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) →
    ε⁻¹ ≤ Real.exp Q →
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) →
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) →
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) →
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt →
    (∀ a, R0 a + 1 / 4 ≤ Ht) →
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let w := fun r : Pos => (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
      coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step c q r.val)
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ t : Σ r : Pos, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e w t‖) ≤ Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (height a : ℝ)) : ℂ) *
          (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then 1 else 0)) -
          (∑ r : Pos, w r * siteFamilyEval (e r) (fun _ => z)
            (fun _ a => (z a : ℝ) / height a))‖ ≤ δout := by
  intro degree height denom torus V cap cutoff R0 ε ζ freq
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt p Pos map w
  let c0 (a : A) := coefficients a (constantCoefficientSlot _ _)
  have hc0 (a : A) : allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c0 a) ≠ 0 := hcoefficients a _
  have heach (r : Pos) := exists_forecastInactive_sliced_fixed_product_site
    B U basis hR hσ S q (NeZero.pos q) r.val H step c hH hsubset r.property selected
    δ P Hchild hδ hreg hsmall hgrid c0 hc0 hσ1 L hL hP hsP hstride hB
    Cactual δout Q Nt Vt Ct Ht Lt hCactual hδout hQ
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt
  choose e he herr using heach
  let mass (r : Pos) := p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val))
  let co (r : Pos) := coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step c q r.val)
  have hmass : (∑ r : Pos, mass r) ≤ 1 :=
    (forecastInactive_positiveResidue_mass_sum p (principalResidueLabel q)).le
  have hm (r : Pos) : 0 ≤ mass r := p.mass_nonneg _
  refine ⟨e, he, ?_, ?_⟩
  · have hbound := forecastSiteMixture_weighted_mass e he (fun _ => hCtNonneg) mass co hm hmass
      (fun r => hcoefficient _)
    simpa only [Finset.prod_const, Finset.card_univ] using hbound
  · intro x z
    let μ (r : Pos) : ℂ := (((∏ a, (height a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r.val
        H step c hH hsubset r.property (selected a).1 (selected a).2
        (Finset.univ : Finset (Finset Empty)) (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ)
    have herr' := forecastSiteMixture_weighted_error e mass co μ hm hmass
      (fun r => hcoefficient _) (fun _ => z) (fun _ a => (z a : ℝ) / height a)
      hδout.le (fun r => herr r z)
    rw [forecastInactive_sliced_fixed_residue_identity B U basis S hR hσ selected hselected q
      H step c hH hsubset coefficient hsmall coefficients hcoefficients x z, Finset.mul_sum]
    have heq : (∑ r : Pos, ((∏ a, (height a : ℝ)) : ℂ) *
        ((mass r : ℂ) * co r *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r.val
            H step c hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c0 a)) (fun a _ => z a)).toReal : ℂ))) =
        ∑ r : Pos, (mass r : ℂ) * co r * μ r := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      push_cast
      ring
    rw [heq]
    exact herr'

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
variable (q : ℕ) [NeZero q]
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ c j + (step j : ℤ) * t.val ∧
    c j + (step j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_forecastInactive_affineInterval_fixed_residue_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) →
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) →
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) →
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) →
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) →
    ε⁻¹ ≤ Real.exp Q →
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) →
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) →
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) →
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt →
    (∀ a, R0 a + 1 / 4 ≤ Ht) →
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let w := fun r : Pos => (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
      coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step c q r.val)
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ t : Σ r : Pos, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e w t‖) ≤ Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (height a : ℝ)) : ℂ) *
          (principalAffineIntervalLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U basis S) H step c hinside hH).complexMean (fun y => coefficient (principalResidueLabel q y) *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then 1 else 0)) -
          (∑ r : Pos, w r * siteFamilyEval (e r) (fun _ => z)
            (fun _ a => (z a : ℝ) / height a))‖ ≤ δout := by
  intro degree height denom torus V cap cutoff R0 ε ζ freq
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt p Pos w
  have hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ) :=
    fun t => integerProgressionSupport_subset_of_fin _ _ _ _ (hinside t)
  rw [principalAffineIntervalLaw_eq_contained B (layerSamplerDegree I n) H hH
    (allocatedPrincipalSides B U basis S) step c (allocatedPrincipalSides_pos B U basis S) hinside hsubset]
  exact exists_forecastInactive_sliced_fixed_residue_site B U basis hR hσ S q H step c hH hsubset
    selected hselected coefficient hcoefficient δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients
    hσ1 L hL hP hsP hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt

end Erdos3.VectorPolynomial

end

end OAI
