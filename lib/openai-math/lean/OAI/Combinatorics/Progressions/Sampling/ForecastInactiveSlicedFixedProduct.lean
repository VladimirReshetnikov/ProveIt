import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedAxisCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

noncomputable def allocatedSupportedPhysicalJointPMF : PMF (∀ a, rows a → ℤ) :=
  (conditioned).toPMF.bind (fun y => dependentProductPMF (fun a =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2)))

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

include hselected hgrid in
theorem allocatedSupportedPhysicalGrid_joint_law :
    allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected rows x =
      dependentProductPMF (fun a => allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell
        (selected a).1 (selected a).2 (rows a) x) := by
  let e (a : A) : LayerSamplerAxis I n := ⟨(selected a).1, Sum.inr (selected a).2⟩
  have he : Function.Injective e := by
    have hi : Function.Injective (fun z : (Σ j : Fin m, Fin (n j)) =>
        (⟨z.1, Sum.inr z.2⟩ : LayerSamplerAxis I n)) := by
      rintro ⟨j, i⟩ ⟨k, l⟩ h
      have hj : j = k := congrArg Sigma.fst h
      subst k
      have hsum : (Sum.inr i : I j ⊕ Fin (n j)) = Sum.inr l :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hl : i = l := Sum.inr.inj hsum
      subst l
      rfl
    exact hi.comp hselected
  let k (a : A) (y : ∀ b : B (e a), ∀ v : Fin (layerSamplerDegree I n (e a)),
      IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨e a, b, v⟩)) : PMF (rows a → ℤ) :=
    (independentProductPMF (fun c : Option (B (e a)) =>
      allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (e a) c))).map
      (fun c t => booleanCoefficient (fun _ : Finset α => c none) t +
        ∑ b, c (some b) * integerBooleanBlockJet (fun v i => (y b v i : ℤ)) t)
  have hpoint (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) :
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)))
        (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) =
      k a (fun b v => y ⟨e a, b, v⟩) := by
    exact allocatedPhysicalGridJetPMF_principal B U basis hR hσ S (selected a).1 (selected a).2
      (hgrid a) x y (fun t : rows a => (t : Finset α))
  unfold allocatedSupportedPhysicalJointPMF allocatedSupportedPhysicalGridPMF
  simp_rw [hpoint]
  exact principalSupportedResidue_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S) q r hcell e he k

include hselected hgrid in
theorem allocatedSupportedPhysicalGrid_joint_mass (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected rows x z).toReal =
      ∏ a, (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell
        (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  rw [allocatedSupportedPhysicalGrid_joint_law B U basis hR hσ S q r hcell selected rows x
    hselected hgrid, dependentProductPMF_apply, ENNReal.toReal_prod]

include hselected hgrid in
theorem allocatedSupportedPhysicalGrid_joint_scaled_mass (z : ∀ a, rows a → ℤ) :
    (∏ a, (basisAxisScale (basis (selected a).1) (selected a).2 : ℝ) ^ (rows a).card) *
      (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected rows x z).toReal =
      ∏ a, (basisAxisScale (basis (selected a).1) (selected a).2 : ℝ) ^ (rows a).card *
        (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell
          (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  rw [allocatedSupportedPhysicalGrid_joint_mass B U basis hR hσ S q r hcell selected rows x
    hselected hgrid, Finset.prod_mul_distrib]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (rows : A → Finset (Finset α))

theorem allocatedJointGrid_site_approximation
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (scale : A → ℕ) (e : A → ScalarSiteExpansion.{uα,uα} (Finset α))
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcap : ∀ a (x : G → IntegerScalarCubeBox α S.value) z,
      ‖((((scale a : ℝ) ^ (rows a).card) *
        (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (selected a).1 (selected a).2
          (rows a) x z).toReal : ℝ) : ℂ)‖ ≤ C)
    (he : ∀ a (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
      (∀ t ∉ rows a, booleanCoefficient y t = 0) →
      ‖((((scale a : ℝ) ^ (rows a).card) *
        (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (selected a).1 (selected a).2
          (rows a) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
        (e a).integerEval (scale a) y‖ ≤ uniformProductAccuracy (Fintype.card A) C δ) :
    ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
      (∀ a t, t ∉ rows a → booleanCoefficient (fun s => y s a) t = 0) →
      ‖((((∏ a, (scale a : ℝ) ^ (rows a).card)) *
        (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected rows x
          (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
        siteFamilyEval e y (fun s a => (y s a : ℝ) / scale a)‖ ≤ δ := by
  intro x y hy
  let g (a : A) : ℂ := ((scale a : ℝ) ^ (rows a).card *
    (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (selected a).1 (selected a).2
      (rows a) x (fun t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ)
  have hprod := siteFamily_approximation e y (fun s a => (y s a : ℝ) / scale a) g
    (Fintype.card A) le_rfl hC hδ (fun a => hcap a x _) (fun a => he a x _ (hy a))
  have heq : ((((∏ a, (scale a : ℝ) ^ (rows a).card)) *
      (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected rows x
        (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U b hR hσ S q r hcell
      selected rows x hselected hgrid _, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [heq]
  exact hprod

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
theorem exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense
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
    let ζ := uniformBlockRetainedBias j.val 1 degree P V V ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val 1 P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val 1 degree P V V
    let R0 := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) * R j
    let K := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (cap + 1))⁻¹ ≤ Real.exp Q →
      (CircleFourier.characterLipConstant * freq + 4 : ℝ≥0) ≤ Real.exp Q →
      (K : ℝ) ≤ Real.exp Q →
      (2 * (K : ℝ≥0) ^ 2 * (K : ℝ≥0) : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds
        (max ((uniformSpectrumSizeConstant j.val 1 degree P V V /
          ε ^ max (majorArcSpectrumExponent j.val 1) (majorArcLengthExponent j.val * degree)) *
          Real.exp (4 * Q + 8)) (Real.exp (4 * Q + 8)))
        (max (uniformScaledRetainedDenominatorBound j.val 1 degree P V V ζ) 1)
        (max (cap * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (z : ℤ),
        ‖(((height : ℝ) *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
            (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval height (fun _ => z)‖ ≤ 2 * ε := by
  intro V ζ freq cap R0 K Q hQ hRQ hεQ hLQ hKQ hKLQ hεinvQ
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) : t.card ≤ degree := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val (Finset.univ : Finset (Finset Empty)).card
      (degree * (Finset.univ : Finset (Finset Empty)).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩) := by
    simpa using hB
  have hh := exists_forecastInactive_sliced_fixed_site_small_or_dense
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i δ P ε Finset.univ Hchild
    hδ hreg hsmall hgrid c0 hc0 hσ1 A hA hP hsP hstride hε hε1 hrows hB' (η := ε) (Q := Q)
  simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one, Nat.cast_one, mul_one, one_mul, Nat.cast_zero, zero_add, one_pow] at hh
  obtain ⟨e, he, herr⟩ := hh hε hQ hRQ hεQ hLQ hKQ hKLQ hεinvQ
  refine ⟨e, he, ?_⟩
  intro z
  have hconst (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => z) t = z := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  have hcconst (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => c0) t = c0 := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  have hz := herr (fun _ => z) (by intro t ht; exact (ht (Finset.mem_univ t)).elim)
  simpa only [hconst, hcconst, two_mul] using hz

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
variable {A : Type*} [Fintype A]

include hq in
theorem exists_forecastInactive_sliced_fixed_product_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c0 : A → ℤ)
    (hc0 : ∀ a, allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c0 a) ≠ 0)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
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
    ∃ e : A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ a, (e a).Bounds Nt Vt Ct Lt Ht) ∧
      ∀ z : A → ℤ,
        ‖(((∏ a, (height a : ℝ)) *
          (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r
            H step c hH hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
            (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ) -
          siteFamilyEval e (fun _ => z) (fun _ a => (z a : ℝ) / height a)‖ ≤ δout := by
  intro degree height denom torus V cap cutoff R0 ε ζ freq
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) hCactual hδout
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε]; linarith
  have heach (a : A) := exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense
    B U basis hR hσ S q hq r H step c hH hsubset hcell (selected a).1 (selected a).2 Hchild
    (c0 a) (hc0 a) (hgrid a) (hsmall a) hδ (hreg a) L hL P hP hsP (hstride a)
    (hB a) hε hε1 (hσ1 a) hQ (hRQ a) (hεQ a) (hLQ a) (hKQ a) (hKLQ a) hεinvQ
  choose e he herr using heach
  refine ⟨e, fun a => (he a).mono (hNt a) (hVt a) (hCt a) hLt (hHt a), ?_⟩
  intro z
  let g (a : A) : ℂ := (((height a : ℝ) *
    (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell
      (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
      (fun _ => c0 a) (fun _ => z a)).toReal : ℝ) : ℂ)
  have hg (a : A) : ‖g a‖ ≤ Cactual :=
    (forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense B U basis hR hσ S q hq r
      H step c hH hsubset hcell (selected a).1 (selected a).2 δ P Hchild hδ (hreg a)
      (hsmall a) (hgrid a) L hL hP hsP (hstride a) (hB a) (c0 a) (z a)).trans (hactual a)
  have herr' (a : A) :
      ‖g a - (e a).eval (fun _ => z a) (fun _ => (z a : ℝ) / height a)‖ ≤
      uniformProductAccuracy (Fintype.card A) Cactual δout := by
    simpa only [ScalarSiteExpansion.integerEval, ε, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using herr a (z a)
  have hp' := siteFamily_approximation e (fun _ => z)
    (fun _ a => (z a : ℝ) / height a) g (Fintype.card A) le_rfl hCactual hδout hg herr'
  have hj : (((∏ a, (height a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r
        H step c hH hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
        (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib,
      Complex.ofReal_prod]
  rw [hj]
  exact hp'

end Erdos3.VectorPolynomial

end

end OAI
