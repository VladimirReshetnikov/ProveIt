import OAI.Combinatorics.Progressions.Dynamics.SiteReferenceErrorBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealReferenceInsertion
import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteBufferFourier
import OAI.Combinatorics.Progressions.Linear.AllocatedSiteEnvelopeKernel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

theorem allocatedPhysicalProfile_integrable_mass (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ v, 0 ≤ f v ∧ f v ≤ (∏ q : output, R q.1.val.1)⁻¹)
    (hs : ∀ v, f v ≠ 0 → ‖fun q : output => v q / R q.1.val.1‖ ≤ T) :
    Integrable (allocatedUnmaskedLongProfileDensity B U b S f) reference ∧
      (∫ z, allocatedUnmaskedLongProfileDensity B U b S f z ∂reference) ≤
        (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
  let box := allocatedPhysicalLongJetBox B U b S O T
  let Jv : ℝ := ∏ q : output, R q.1.val.1
  have hJv : 0 < Jv := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hbox := allocatedPhysicalLongJetBox_measurable B U b S O T
  have hg : Integrable (box.indicator (fun _ => Jv⁻¹)) reference :=
    (integrableOn_const (allocatedPhysicalLongJetBox_measure_lt_top B U b S O T).ne).integrable_indicator hbox
  have hdom (z : AllocatedLongJetRows B U b S O) :
      f (allocatedLongJetRealCoordinates B U b S z) ≤ box.indicator (fun _ => Jv⁻¹) z := by
    by_cases hz : f (allocatedLongJetRealCoordinates B U b S z) = 0
    · rw [hz]
      exact Set.indicator_nonneg (fun _ _ => (inv_pos.mpr hJv).le) z
    · have hmem := allocatedPhysicalLongJetBox_of_normalizedCoordinates B U b S O hR hT z (hs _ hz)
      rw [Set.indicator_of_mem hmem]
      exact (hb _).2
  have hi : Integrable (fun z => f (allocatedLongJetRealCoordinates B U b S z)) reference := by
    apply hg.mono' (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by rw [Function.comp_apply, Real.norm_of_nonneg (hb _).1]; exact hdom z)
  refine ⟨hi.div_const scale, ?_⟩
  change (∫ z, f (allocatedLongJetRealCoordinates B U b S z) / scale ∂reference) ≤ _
  rw [integral_div]
  apply (div_le_iff₀ hscale).mpr
  calc
    _ ≤ ∫ z, box.indicator (fun _ => Jv⁻¹) z ∂reference := integral_mono hi hg hdom
    _ = Jv⁻¹ * (reference).real box := by
      rw [integral_indicator hbox, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ Jv⁻¹ * ((2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * Jv * scale) :=
      mul_le_mul_of_nonneg_left
        (allocatedPhysicalLongJetBox_measure_bound B U b S O hR hσ1 hT) (inv_nonneg.mpr hJv.le)
    _ = _ := by field_simp [hJv.ne']

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹
local notation "radius" => idealSiteEnvelopeRadius α m

local notation "reference" => allocatedLongJetReference B U b S jets

theorem allocatedSiteBuffer_integrable_mass (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1) :
    Integrable (allocatedUnmaskedLongProfileDensity B U b S (allocatedSiteBuffer (α := α) B U b S)) reference ∧
      (∫ z, allocatedUnmaskedLongProfileDensity B U b S (allocatedSiteBuffer (α := α) B U b S) z ∂reference) ≤
        (4 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) := by
  have h := allocatedPhysicalProfile_integrable_mass (O := jets) B U b S hR hσ1 (T := 2 * radius)
    (allocatedSiteBuffer (α := α) B U b S) (allocatedSiteBuffer_measurable (α := α) B U b S)
    (mul_nonneg (by norm_num) (idealSiteEnvelopeRadius_pos α m).le)
    (allocatedSiteBuffer_range (α := α) B U b S hR) (allocatedSiteBuffer_support (α := α) B U b S)
  simpa only [show 2 * (2 * radius) + 1 = 4 * radius + 1 by ring] using h

theorem allocatedSiteBuffer_integral_le_exp (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1) :
    (∫ z, allocatedUnmaskedLongProfileDensity B U b S (allocatedSiteBuffer (α := α) B U b S) z ∂reference) ≤
      Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) *
        (((m : ℝ) + 3) * Fintype.card α + 6)) :=
  (allocatedSiteBuffer_integrable_mass B U b S hR hσ1).2.trans
    (idealSiteBuffer_volume_le_exp α m _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_reference_buffer_mass :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {D pNum Psp sLog : ℝ}
    (_hdims : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (_hpNum : 0 ≤ pNum) (_hPsp : 0 ≤ Psp) (_hsLog : 0 ≤ sLog)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum) (_hSlog : (S.value : ℝ) ≤ Real.exp sLog)
    (_hσ1 : ∀ j, σ j ≤ 1) (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (_hqDim : dim ≤ m + 1)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hClog : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVlog : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    (_hperiodSize : modulus ≤ Mk ^ (m + 1))
    (_hperiodSp : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    (_hdegreePsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp) (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (Dsp : ℝ) (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ)),
    let gain := allocatedSiteEnvelopeGain m D Psp
    let input := allocatedSiteBufferInput m D pNum gain sLog (normalizedSiteCutoffBound : ℝ)
    let budget := allocatedProfileFourierOutput input
    budget ≤ P →
    ∀ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ, (∀ w, ‖test w‖ ≤ 1) → ∀ u r,
      (∑ t : cells × spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4,
        ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hMk selection hx modulus q
          reference N _hW spatialMesh base cells test u r t‖ *
        |allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d
          (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r)
            (allocatedSiteBuffer (α := Fin dim) B U b S))
          (physicalCubeEuclideanSample U d p hm
            (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))|) ≤
        Real.exp (siteReferenceMassLog m D Psp) := by
  obtain ⟨K, hK, hwindow⟩ := exists_allocated_reference_profile_window_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x D pNum Psp sLog hdims hpNum hPsp hsLog hRi hSlog hσ1 hJ
    Mk hMk selection hx hMkPsp hqDim _ hb o Q _ bW d _ C V hC hV hClog hVlog ν _ _ modulus _ hperiod hperiodSize hperiodSp
    X _ _ q hq reference residue N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass
    p hp hm P Rrank hP hX hdim hτP hstride hsize hrank hRank spatialMesh hspatialMesh
    hdegreePsp hdimPsp hGPsp hXPsp Dsp hDsp hWscale gain input budget hinput test htest u r
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let Cm : ℝ≥0 := ⟨Real.exp w, (Real.exp_pos w).le⟩
  let A : ℝ≥0 := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) *
    Cm ^ Fintype.card (LayerSamplerAxis I n)
  let buffer := allocatedSiteBuffer (α := Fin dim) B U b S
  let cap : ℝ≥0 := ‖(∏ t : (Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1), R t.1.val.1)⁻¹‖₊
  let lip := allocatedSiteBufferLip (α := Fin dim) B U b S ⟨Real.exp pNum, (Real.exp_pos pNum).le⟩
  let Merr : ℝ := A * Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) *
    (((m : ℝ) + 3) * Fintype.card (Fin dim) + 6))
  let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    (((1 + W) / S.value) ^ dim) ^ Fintype.card X
  let Csp := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hCm : 1 ≤ (Cm : ℝ) := Real.one_le_exp_iff.mpr hw
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)
  have hAg : (A : ℝ) ≤ Real.exp gain :=
    allocatedProfileGain_le_exp B hdims hQ Mk modulus hperiodSize Cm hPsp hw hMkPsp le_rfl
  have hmasks uu rr j z :=
    And.intro (allocatedIntegerKernelMask_bound B U b S x jetRows hMk selection hx
      (by simpa only [Fintype.card_fin] using hqDim) (fun _ => Subtype.val_injective)
      (fun _ z => z.property) j modulus (residue uu rr j) z).1
      (allocatedIntegerKernelMask_le_exp B U b S x jetRows hMk selection hx
        (by simpa only [Fintype.card_fin] using hqDim) (fun _ => Subtype.val_injective)
        (fun _ z => z.property) hMkPsp j modulus (residue uu rr j) z)
  have hg : 0 ≤ gain := allocatedSiteEnvelopeGain_nonneg m hdims.nonneg hPsp
  obtain ⟨hL, h4Q, _hpQ, _hDQ, hamb, hδ, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteBuffer_fourier_budget (α := Fin dim) B U b S hdims hpNum hg hsLog hJ
      (fun j => (hR j).le) hRi A hAg hSlog C V hClog hVlog
  have hquarterP : 1 / (1 / 4 : ℝ) ≤ Real.exp P := by
    norm_num
    exact (h4Q.trans hinput).trans (by linarith [Real.add_one_le_exp P])
  have heq : (fun z => |buffer z - 0|) = buffer := by
    funext z
    rw [sub_zero, abs_of_nonneg (allocatedSiteBuffer_range B U b S hR z).1]
  have hwindowBound := hwindow (ε := (1 / 4 : ℝ)) B U b hR hσ S x hMk selection hx hb o bW d C V hC hV ν
    modulus hperiod hperiodSp q hq reference residue N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm hP hX hdim hτP hstride (by norm_num) hquarterP hsize hrank hRank
    spatialMesh hspatialMesh Cm hCm hmasks (fun _ => buffer) (fun _ _ => 0) cap 0 lip 0
    (fun _ => allocatedSiteBuffer_lipschitz B U b S hR _ hRi) (fun _ => LipschitzWith.const 0)
    (fun _ => allocatedSiteBuffer_abs_le B U b S hR) (by intro _ _; simp)
    (δf := (1 / 4 : ℝ)) (L := allocatedProfileFourierInput input) (by norm_num) hL hamb hδ
    hLip (hfreq.trans (Real.exp_le_exp.mpr hinput)) (hcoeff.trans (Real.exp_le_exp.mpr hinput))
    (by intro _; rw [heq]; exact (allocatedSiteBuffer_integrable_mass B U b S hR hσ1).1)
    Merr (by
      intro _
      rw [heq]
      exact mul_le_mul_of_nonneg_left
        (allocatedSiteBuffer_integral_le_exp B U b S hR hσ1) A.coe_nonneg) test htest u r
  have hsmall : Merr + 2 * (1 / 4 : ℝ) + 1 / 4 ≤ Real.exp (allocatedSiteEnvelopeMassLog m D Psp) :=
    allocatedSiteEnvelope_sample_mass_le m hdims.nonneg hPsp hdims.outputs hdims.cube hAg
  have hS1 : 1 ≤ (S.value : ℝ) := by exact_mod_cast S.positive
  have hperiodPsp := coefficientErrorPeriod_exp_sq hPsp hdegreePsp hMkPsp hperiodSize
  have hsp : 0 ≤ Csp * Vsp ∧ Csp * Vsp ≤ Real.exp (coefficientErrorSpatialLog Psp) :=
    coefficientErrorSpatialFactor_exp_bound dim X selection hPsp hMk hMkPsp hperiodPsp
      hdimPsp hGPsp hXPsp hS1 hW hDsp hWscale
  have hcombined : Csp * (Vsp * (Merr + 2 * (1 / 4 : ℝ) + 1 / 4)) ≤ Real.exp (siteReferenceMassLog m D Psp) := by
    calc
      _ = (Csp * Vsp) * (Merr + 2 * (1 / 4 : ℝ) + 1 / 4) := by ring
      _ ≤ (Csp * Vsp) * Real.exp (allocatedSiteEnvelopeMassLog m D Psp) :=
        mul_le_mul_of_nonneg_left hsmall hsp.1
      _ ≤ Real.exp (coefficientErrorSpatialLog Psp) * Real.exp (allocatedSiteEnvelopeMassLog m D Psp) :=
        mul_le_mul_of_nonneg_right hsp.2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; rfl
  have hzero : (fun uu rr => allocatedCoveredProfileDensity B U b hR hσ S x uu (reference uu rr) jetRows hb o bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
      (allocatedLongProfileDensity B U b S x jetRows modulus (residue uu rr) (fun _ => 0))) =
      (fun _ _ _ => 0) := by
    funext uu rr y
    have hlzero : allocatedLongProfileDensity B U b S x jetRows modulus (residue uu rr)
        (fun _ => 0) = (fun _ => 0) := by
      funext z
      simp only [allocatedLongProfileDensity, mul_zero, zero_div]
    rw [hlzero]
    exact allocatedCoveredProfileDensity_zero B U b hR hσ S x uu (reference uu rr) jetRows hb o bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) y
  rw [hzero] at hwindowBound
  exact (show _ ≤ _ by simpa only [allocatedRefinedCoveredError, sub_zero] using hwindowBound).trans hcombined

end Erdos3.VectorPolynomial

end

end OAI
