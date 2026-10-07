import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus
import OAI.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
import OAI.Combinatorics.Progressions.Polynomial.BooleanJetHighDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

abbrev BoundedBooleanJet (α : Type*) (h : ℕ) := {s : Finset α // s.card ≤ h}

noncomputable def booleanReconstructionMatrix (α : Type*) [DecidableEq α] :
    Matrix (Finset α) (Finset α) ℤ := fun s r => if r ⊆ s then 1 else 0

theorem booleanJetExtraction_mul_reconstruction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanJetExtractionMatrix (id : Finset α → Finset α) * booleanReconstructionMatrix α = 1 := by
  ext s r
  change (booleanJetExtractionMatrix id *ᵥ (fun t => if r ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  rfl

theorem booleanReconstruction_mul_extraction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanReconstructionMatrix α * booleanJetExtractionMatrix (id : Finset α → Finset α) = 1 :=
  mul_eq_one_comm.mp booleanJetExtraction_mul_reconstruction

noncomputable def boundedBooleanReconstructionMatrix (α : Type*) [DecidableEq α] (h : ℕ) :
    Matrix (Finset α) (BoundedBooleanJet α h) ℤ := fun s r => if r.val ⊆ s then 1 else 0

theorem boundedBooleanReconstruction_siteMatrix {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) :
    boundedBooleanReconstructionMatrix α h *
        booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) := by
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let F := booleanJetExtractionMatrix (id : Finset α → Finset α) * E
  have hz (r : Finset α) (hr : h < r.card) (e) : F r e = 0 := by
    change (booleanJetExtractionMatrix id *ᵥ (fun t => E t e)) r = 0
    rw [booleanJetExtractionMatrix_mulVec]
    exact BooleanCubeKernel.boundedSiteMatrix_high_jet_zero root D h e r hr
  rw [Matrix.mul_assoc]
  ext s e
  change (∑ r : BoundedBooleanJet α h, booleanReconstructionMatrix α s r.val * F r.val e) = E s e
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : Finset α => r.card ≤ h),
        booleanReconstructionMatrix α s r * F r e :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ r : Finset α, booleanReconstructionMatrix α s r * F r e := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r _ hr
      have hh : h < r.card := by simpa using hr
      rw [hz r hh, mul_zero]
    _ = (booleanReconstructionMatrix α * F) s e := rfl
    _ = E s e := by
      dsimp only [F]
      rw [← Matrix.mul_assoc, booleanReconstruction_mul_extraction, Matrix.one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem boundedBooleanExtraction_mul_reconstruction {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) :
    booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *
      boundedBooleanReconstructionMatrix α h = 1 := by
  ext s r
  change (booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *ᵥ
    (fun t => if r.val ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  simp only [Matrix.one_apply, Subtype.val_inj]

theorem booleanJetExtractionMatrix_abs_le_one {α O : Type*} [DecidableEq α]
    (rows : O → Finset α) (r : O) (s : Finset α) :
    |(booleanJetExtractionMatrix rows r s : ℝ)| ≤ 1 := by
  unfold booleanJetExtractionMatrix
  split_ifs <;> simp

theorem boundedBooleanReconstruction_zsmul_inverse {α W : Type*}
    [Fintype α] [DecidableEq α] [AddCommGroup W]
    (h : ℕ) (x : BoundedBooleanJet α h → W) (r : BoundedBooleanJet α h) :
    (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val r s •
      ∑ t : BoundedBooleanJet α h, boundedBooleanReconstructionMatrix α h s t • x t) = x r := by
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  change (∑ t, (booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *
    boundedBooleanReconstructionMatrix α h) r t • x t) = x r
  rw [boundedBooleanExtraction_mul_reconstruction]
  simp [Matrix.one_apply]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def boundedBooleanJetRows (α : Type*) [Fintype α] (h : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun s => s.card ≤ h)

theorem mem_boundedBooleanJetRows {α : Type*} [Fintype α] (h : ℕ) (s : Finset α) :
    s ∈ boundedBooleanJetRows α h ↔ s.card ≤ h := by
  simp only [boundedBooleanJetRows, Finset.mem_filter, Finset.mem_univ, true_and]

theorem boundedBooleanJetRows_subtype_eq (α : Type*) [Fintype α] (h : ℕ) :
    {s : Finset α // s ∈ boundedBooleanJetRows α h} = BoundedBooleanJet α h := by
  simp only [mem_boundedBooleanJetRows, BoundedBooleanJet]

noncomputable def boundedBooleanJetRowsEquiv (α : Type*) [Fintype α] (h : ℕ) :
    {s : Finset α // s ∈ boundedBooleanJetRows α h} ≃ BoundedBooleanJet α h where
  toFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mp s.property⟩
  invFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundedBooleanJetRowsEquiv_val (α : Type*) [Fintype α] (h : ℕ)
    (s : {s : Finset α // s ∈ boundedBooleanJetRows α h}) :
    (boundedBooleanJetRowsEquiv α h s).val = s.val := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def realBoundedSiteReconstruction {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) (v : BoundedBooleanJet α h → ℝ) (s : Finset α) : ℝ :=
  ∑ r : BoundedBooleanJet α h, v r * (if r.val ⊆ s then 1 else 0)

theorem realBoundedSiteReconstruction_coefficient {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) (v : BoundedBooleanJet α h → ℝ) (s : BoundedBooleanJet α h) :
    booleanCoefficient (realBoundedSiteReconstruction h v) s.val = v s := by
  unfold realBoundedSiteReconstruction
  rw [booleanCoefficient_sum]
  simp only [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro r _ hrs
    have hsr : s.val ≠ r.val := fun he => hrs (Subtype.ext he.symm)
    simp only [hsr, ite_false, mul_zero]
  · simp

noncomputable def realSitesFromBoundedJets {D α : Type*} [Fintype α] [DecidableEq α]
    (h : D → ℕ) (v : (Σ d, BoundedBooleanJet α (h d)) → ℝ) : Finset α → D → ℝ :=
  fun s d => realBoundedSiteReconstruction (h d) (fun r => v ⟨d, r⟩) s

theorem booleanSiteJets_realSitesFromBoundedJets {D α : Type*} [Fintype α] [DecidableEq α]
    (h : D → ℕ) (v : (Σ d, BoundedBooleanJet α (h d)) → ℝ) :
    booleanSiteJets (fun d => (Subtype.val : BoundedBooleanJet α (h d) → Finset α))
      (realSitesFromBoundedJets h v) = v := by
  funext o
  exact realBoundedSiteReconstruction_coefficient (h o.1) (fun r => v ⟨o.1, r⟩) o.2

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev LowBooleanJetTorus (α : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  BooleanJetTorus (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) U

noncomputable def siteFromLowBooleanJets {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    LowBooleanJetTorus α U →+ SiteTorus (Finset α) U where
  toFun y j := integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1)) (y j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

theorem siteFromLowBooleanJets_continuous {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : Continuous (siteFromLowBooleanJets (α := α) U) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp (continuous_apply j))

theorem siteFromLowBooleanJets_coefficient {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    siteFromLowBooleanJets U (coefficientBooleanJetTorusMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x) =
      coefficientSiteTorusMap U (integerAffineCube root D) x := by
  funext j
  change integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1))
    (integerMatrixTorusMap (U j)
      (booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
        (coefficientLayerTorus U j x))) = _
  rw [integerMatrixTorusMap_comp, integerMatrixTorusMap_comp,
    boundedBooleanReconstruction_siteMatrix]
  rfl

theorem coefficientSiteImage_lowJet_injective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Injective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E y z hyz
  obtain ⟨x, hx⟩ := y.property
  obtain ⟨w, hw⟩ := z.property
  apply Subtype.ext
  have he := congrArg (siteFromLowBooleanJets U) hyz
  dsimp only at he
  rw [← hx, ← hw] at he ⊢
  exact (siteFromLowBooleanJets_coefficient U root D x).symm.trans
    (he.trans (siteFromLowBooleanJets_coefficient U root D w))

theorem coefficientSiteImage_lowJet_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Surjective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E z
  obtain ⟨x, hx⟩ := coefficientBooleanJetTorusMap_surjective U root D a ha hperiod
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
    (fun _ => Subtype.val_injective) (fun _ o => o.property) z
  exact ⟨Set.rangeFactorization E x, hx⟩

noncomputable def lowJetSiteImageSection {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (z : LowBooleanJetTorus α U) :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) :=
  ⟨siteFromLowBooleanJets U z, by
    obtain ⟨x, hx⟩ := coefficientBooleanJetTorusMap_surjective U root D a ha hperiod
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (fun _ => Subtype.val_injective) (fun _ o => o.property) z
    exact ⟨x, (siteFromLowBooleanJets_coefficient U root D x).symm.trans
      (congrArg (siteFromLowBooleanJets U) hx)⟩⟩

theorem lowJetSiteImageSection_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    Continuous (lowJetSiteImageSection U root D a ha hperiod) :=
  (siteFromLowBooleanJets_continuous U).subtype_mk _

theorem lowJetSiteImageSection_site {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (y : Set.range (coefficientSiteTorusMap U (integerAffineCube root D))) :
    lowJetSiteImageSection U root D a ha hperiod
      (siteBooleanJetTorusMap U
        (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) = y := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := y.property
  change siteFromLowBooleanJets U _ = y.val
  rw [← hx]
  exact siteFromLowBooleanJets_coefficient U root D x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem realBoundedSiteReconstruction_bound {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) (v : BoundedBooleanJet α h → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ r, |v r| ≤ C) (s : Finset α) :
    |realBoundedSiteReconstruction h v s| ≤ (2 : ℝ) ^ Fintype.card α * C := by
  have hcard : Fintype.card (BoundedBooleanJet α h) ≤ 2 ^ Fintype.card α := by
    simpa using Fintype.card_le_of_injective
      (fun r : BoundedBooleanJet α h => r.val) Subtype.val_injective
  unfold realBoundedSiteReconstruction
  calc
    _ ≤ ∑ r : BoundedBooleanJet α h, |v r * (if r.val ⊆ s then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : BoundedBooleanJet α h, C := by
      apply Finset.sum_le_sum
      intro r _
      split_ifs <;> simp only [mul_one, mul_zero, abs_zero]
      · exact hv r
      · exact hC
    _ = (Fintype.card (BoundedBooleanJet α h) : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

theorem realBoundedSiteReconstruction_sub {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) (v w : BoundedBooleanJet α h → ℝ) (s : Finset α) :
    realBoundedSiteReconstruction h v s - realBoundedSiteReconstruction h w s =
      realBoundedSiteReconstruction h (fun r => v r - w r) s := by
  unfold realBoundedSiteReconstruction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem realSitesFromBoundedJets_bound {D α : Type*} [Fintype α] [DecidableEq α]
    (h : D → ℕ) (v : (Σ d, BoundedBooleanJet α (h d)) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hv : ∀ o, |v o| ≤ C) (s : Finset α) (d : D) :
    |realSitesFromBoundedJets h v s d| ≤ (2 : ℝ) ^ Fintype.card α * C :=
  realBoundedSiteReconstruction_bound (h d) (fun r => v ⟨d, r⟩) hC (fun r => hv ⟨d, r⟩) s

theorem realSitesFromBoundedJets_lipschitz {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    (h : D → ℕ) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (realSitesFromBoundedJets (α := α) h) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change dist (realSitesFromBoundedJets h v) (realSitesFromBoundedJets h w) ≤
    (2 : ℝ) ^ Fintype.card α * dist v w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro s
  apply (dist_pi_le_iff (by positivity)).mpr
  intro d
  change |realBoundedSiteReconstruction (h d) (fun r => v ⟨d, r⟩) s -
    realBoundedSiteReconstruction (h d) (fun r => w ⟨d, r⟩) s| ≤ _
  rw [realBoundedSiteReconstruction_sub]
  apply realBoundedSiteReconstruction_bound (h d) _ dist_nonneg
  intro r
  simpa only [Real.dist_eq] using dist_le_pi_dist v w ⟨d, r⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def euclideanCoefficientJetMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    CoefficientTorus (K := K) U →+ EuclideanJetLayers U O :=
  (euclideanJetEquiv U).toAddMonoidHom.comp (coefficientBooleanJetTorusMap U root D rows)

theorem euclideanCoefficientJetMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv_continuous U).comp (coefficientBooleanJetTorusMap_continuous U root D rows)

theorem euclideanCoefficientJetMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv U).surjective.comp
    (coefficientBooleanJetTorusMap_surjective U root D a ha hperiod rows hinj hdegree)

theorem euclideanCoefficientJetMap_measurePreserving {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientJetMap U root D rows) μ
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
  have hc := euclideanCoefficientJetMap_continuous U root D rows
  have hs := euclideanCoefficientJetMap_surjective U root D a ha hperiod rows hinj hdegree
  let : CompactSpace (EuclideanJetLayers U O) := by
    have h := isCompact_univ.image hc
    rw [Set.image_univ, Set.range_eq_univ.mpr hs] at h
    exact ⟨h⟩
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : O j => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : ∀ j, (Measure.pi (fun _ : O j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving hc hs (by simp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
variable (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)

noncomputable def euclideanSiteImageEquiv :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) :=
  (Equiv.ofBijective (fun y => siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val)
    ⟨coefficientSiteImage_lowJet_injective U root D,
      coefficientSiteImage_lowJet_surjective U root D a ha hperiod⟩).trans
    (euclideanJetEquiv U).toEquiv

theorem euclideanSiteImageEquiv_continuous :
    Continuous (euclideanSiteImageEquiv U root D a ha hperiod) :=
  (euclideanJetEquiv_continuous U).comp
    ((siteBooleanJetTorusMap_continuous U _).comp continuous_subtype_val)

noncomputable def euclideanSiteImageHomeomorph [CompactSpace (CoefficientTorus (K := K) U)] :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃ₜ
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) := by
  let : CompactSpace (Set.range (coefficientSiteTorusMap U (integerAffineCube root D))) :=
    isCompact_iff_compactSpace.mp (isCompact_range (coefficientSiteTorusMap_continuous U _))
  exact Continuous.homeoOfEquivCompactToT2 (f := euclideanSiteImageEquiv U root D a ha hperiod)
    (euclideanSiteImageEquiv_continuous U root D a ha hperiod)

theorem euclideanSiteImageHomeomorph_sample [CompactSpace (CoefficientTorus (K := K) U)]
    (x : CoefficientTorus (K := K) U) :
    euclideanSiteImageHomeomorph U root D a ha hperiod
      (Set.rangeFactorization (coefficientSiteTorusMap U (integerAffineCube root D)) x) =
      euclideanCoefficientJetMap U root D
        (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x := rfl

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]

theorem euclideanSiteImageHomeomorph_haar
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    (μ.map (Set.rangeFactorization (coefficientSiteTorusMap U (integerAffineCube root D)))).map
        (euclideanSiteImageHomeomorph U root D a ha hperiod) =
      Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) := by
  have hπ := (coefficientSiteTorusMap_continuous U (integerAffineCube root D)).rangeFactorization.measurable
  have he := (euclideanSiteImageHomeomorph U root D a ha hperiod).continuous.measurable
  exact (Measure.map_map he hπ).trans
    (euclideanCoefficientJetMap_measurePreserving U root D a ha hperiod
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (fun _ => Subtype.val_injective) (fun _ o => o.property) μ ν).map_eq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem realBoundedSiteReconstruction_div {α : Type*} [Fintype α] [DecidableEq α]
    (h : ℕ) (v : BoundedBooleanJet α h → ℝ) (c : ℝ) (s : Finset α) :
    realBoundedSiteReconstruction h (fun r => v r / c) s =
      realBoundedSiteReconstruction h v s / c := by
  simp only [realBoundedSiteReconstruction, Finset.sum_div, div_mul_eq_mul_div]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def mixedBooleanSiteValue
    (z : ∀ j : Fin m, (I j → BoundedBooleanJet α (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedBooleanJet α (j.val + 1) → ℤ))
    (s : Finset α) : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
  fun j => mixedArrayRegroup _ _ _
    (mixedArrayIntegerImage (boundedBooleanReconstructionMatrix α (j.val + 1)) (z j)) s

theorem mixedBooleanSiteValue_real
    (z : ∀ j : Fin m, (I j → BoundedBooleanJet α (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedBooleanJet α (j.val + 1) → ℤ))
    (s : Finset α) (j : Fin m) (i : I j) :
    (mixedBooleanSiteValue z s j).1 i = realBoundedSiteReconstruction (j.val + 1) ((z j).1 i) s := by
  simp only [mixedBooleanSiteValue, mixedArrayIntegerImage, mixedArrayRegroup_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply, realBoundedSiteReconstruction,
    boundedBooleanReconstructionMatrix]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

theorem mixedBooleanSiteValue_integer
    (z : ∀ j : Fin m, (I j → BoundedBooleanJet α (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedBooleanJet α (j.val + 1) → ℤ))
    (s : Finset α) (j : Fin m) (i : Fin (n j)) :
    ((mixedBooleanSiteValue z s j).2 i : ℝ) =
      realBoundedSiteReconstruction (j.val + 1) (fun r => ((z j).2 i r : ℝ)) s := by
  simp only [mixedBooleanSiteValue, mixedArrayIntegerImage, mixedArrayRegroup_apply,
    Matrix.mulVec, dotProduct, realBoundedSiteReconstruction, boundedBooleanReconstructionMatrix,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

end VectorPolynomial
end Erdos3

end

end OAI
