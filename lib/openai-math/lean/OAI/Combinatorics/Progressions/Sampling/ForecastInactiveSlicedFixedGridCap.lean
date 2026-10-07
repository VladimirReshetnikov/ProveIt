/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite

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
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

theorem forecastInactive_sliced_fixed_grid_mass_le
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
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
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P)
    (hstride : ∀ a b v, (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual : ℝ) (_hCactual : 0 ≤ Cactual) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    (∏ a, (height a : ℝ)) * law.fiberMean
      (forecastInactiveFixedOutput B U basis S selected coefficients x)
      (fun a _ => z a) (fun _ => 1) ≤ Cactual ^ Fintype.card A := by
  intro degree height denom torus V cap cutoff hactual x z p map law
  let r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod 1 := 0
  let cell : Finset (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty H) :=
    Finset.univ.filter (fun y => principalResidueLabel 1 y = r₀)
  have hcellEq : cell = Finset.univ := by
    ext y
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Subsingleton.elim _ _)
  have hcellMass : p.mass cell = 1 := by
    rw [hcellEq]
    exact p.total
  have hcell : 0 < p.mass cell := by rw [hcellMass]; exact zero_lt_one
  let c₀ (a : A) := coefficients a (constantCoefficientSlot _ _)
  let μ (a : A) := allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S 1 r₀ H step c hH
    hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a)
  let F := forecastInactiveFixedOutput B U basis S selected coefficients x
  have hjoint : ((p.condition cell hcell).fiberLaw map).toPMF.map F = dependentProductPMF μ := by
    have hj := forecastInactiveSlicedFixedPath_joint_law B U basis hR hσ S 1 r₀ H step c hH hsubset hcell
      selected hselected hsmall coefficients hcoefficients x (fun _ => (Finset.univ : Finset (Finset Empty)))
    have hconst (v : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => v) t = v := by
      simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
    unfold F forecastInactiveFixedOutput
    simpa only [hconst, containedSupportedProgressionLaw, p, map, cell, c₀, μ] using hj
  have hmass : law.fiberMean F (fun a _ => z a) (fun _ => 1) =
      (dependentProductPMF μ (fun a _ => z a)).toReal := by
    rw [← hjoint, FiniteProbabilityWeights.toPMF_map_toReal,
      FiniteProbabilityWeights.fiberLaw_mean, FiniteProbabilityWeights.condition_mean,
      hcellMass, hcellEq]
    simp only [Finset.mem_univ, ite_true, div_one]
    simp only [FiniteProbabilityWeights.fiberMean, law, FiniteProbabilityWeights.fiberLaw_mean]
    congr 1
    funext y
    split_ifs <;> rfl
  have haxis (a : A) : (height a : ℝ) * (μ a (fun _ => z a)).toReal ≤ Cactual := by
    have ha := forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense
      B U basis hR hσ S 1 zero_lt_one r₀ H step c hH hsubset hcell (selected a).1 (selected a).2
      δ P Hchild hδ (hreg a) (hsmall a) (hgrid a) L hL hP hsP
      (by simpa only [mul_one] using hstride a) (hB a) (c₀ a) (z a)
    have hab : (height a : ℝ) * (μ a (fun _ => z a)).toReal ≤ max (cutoff a : ℝ) (cap a) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg), Nat.cast_one] using ha
    exact hab.trans (hactual a)
  change (∏ a, (height a : ℝ)) * law.fiberMean F (fun a _ => z a) (fun _ => 1) ≤ _
  rw [hmass, dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _a : A, Cactual :=
      Finset.prod_le_prod₀ (fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
        (fun a _ => haxis a)
    _ = Cactual ^ Fintype.card A := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3.VectorPolynomial

end

end OAI
