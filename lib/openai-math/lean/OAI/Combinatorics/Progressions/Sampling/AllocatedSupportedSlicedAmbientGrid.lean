import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedUniformPhysicalSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem exists_allocated_grid_mean_ambient_factor
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (us : A → PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
        (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d),
        z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) →
        g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
          p.mean (fun a => allocatedGridJetDensity B U b hR hσ S x (us a) v rows
            (fun a => coefficientJetAxisEquiv O I n z.1 a.val)) := by
  intro K D
  have hex (a : A) := exists_allocated_ambient_grid_factor_uniform
    B U b hR hσ S (us a) rows o C hC
  choose g hg hgb hgv using hex
  refine ⟨fun z => p.mean (fun a => g a z), p.mean_lipschitz_uniform _ hg, ?_, ?_⟩
  · intro z
    exact ⟨p.mean_nonneg (fun a => (hgb a z).1),
      (p.mean_mono (fun a => (hgb a z).2)).trans_eq (p.mean_const 1)⟩
  · intro x v hb Q _ bW d _ z hz
    unfold FiniteProbabilityWeights.mean
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun t : ℝ => p.weight a * t)
      (allocatedAmbientGridFactor_chart B U b hR hσ S (us a) rows o (g a) (hgv a) x v hb bW d z hz)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem exists_allocated_grid_times_ambient_lift
    (gridDensity : AllocatedFrozenJetRows B U b S O → ℝ)
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ) {Lg : ℝ≥0}
    (hg : LipschitzWith Lg g) (hgb : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hgv : ∀ z : MixedCoveredJetSource I O Q n d,
      z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) →
      g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
        gridDensity ((coefficientJetAxisSplit O I n grid z.1).1))
    (model : EuclideanJetLayers U O → ℂ)
    (F : (JetAmbientIndex O J → UnitAddCircle) → ℂ) {Lf Cf : ℝ≥0}
    (hF : LipschitzWith Lf F) (hFb : ∀ z, ‖F z‖ ≤ Cf)
    (hFv : ∀ y, model y = F (coveredJetAmbientTorus U 1 y))
    (hzero : ∀ y, y ∉ mixedCoveredJetChart U o b hb bW d ''
      mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) → model y = 0) :
    ∃ G : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith (Cf * (Lg * d) + Lf) G ∧ (∀ z, ‖G z‖ ≤ Cf) ∧
      ∀ y, model y * (allocatedChartGridMultiplier B U b S O hb o bW d gridDensity y : ℂ) =
        G (coveredJetAmbientTorus U 1 y) := by
  have hgC : LipschitzWith (Lg * d)
      (fun z : JetAmbientIndex O J → UnitAddCircle => (g (d • z) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (hg.comp (ambient_nsmul_lipschitz d))
  have hgbC (z : JetAmbientIndex O J → UnitAddCircle) : ‖(g (d • z) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgb _).1]
    exact (hgb _).2
  refine ⟨fun z => F z * (g (d • z) : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul] using lipschitz_mul_of_bounds _ _ hF hgC hFb hgbC
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hFb z) (hgbC z) (norm_nonneg _) (NNReal.coe_nonneg _)).trans_eq (mul_one _)
  · intro y
    dsimp only
    by_cases hy : y ∈ mixedCoveredJetChart U o b hb bW d ''
        mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [← coveredJetAmbientTorus_nsmul_output, hgv z hz,
        allocatedChartGridMultiplier_apply B U b S O hb o bW d gridDensity z hz, hFv]
    · rw [← hFv, hzero y hy, zero_mul, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include v₀ in
theorem exists_allocated_supported_sliced_ambient_grid
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)
    ∃ g : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card gridAxes * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z : MixedCoveredJetSource I rowTypes Q n d, z ∈ region →
        g (coveredJetAmbientTorus U d (chart z)) =
          gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) := by
  classical
  intro K D
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_grid_mean_ambient_factor
    B U b hR hσ S rows o gridLaw id C hC
  refine ⟨g, hg, hgb, ?_⟩
  intro z hz
  exact (hgv x v₀ hb bW d z hz).trans
    (allocatedSupportedSlicedFullGridDensity_mean B U b hR hσ S rowSets H step c hH hsubset q r hcell
      x v₀ _)

include hu₀ hperiod in

theorem allocatedSupportedSlicedProfile_ambient_surrogate_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (rad : ℝ≥0) (hrad : 0 < rad)
    (g : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℝ)
    (hgb : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hgv : ∀ z : MixedCoveredJetSource I rowTypes Q n d, z ∈ region →
      g (coveredJetAmbientTorus U d (chart z)) =
        gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1))
    (model : EuclideanJetLayers U rowTypes → ℂ)
    (F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ)
    (hFv : ∀ y, model y = F (coveredJetAmbientTorus U 1 y))
    (hzero : ∀ y, y ∉ chart '' region → model y = 0)
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y -
      model y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        F (coveredJetAmbientTorus U 1 y) * (g (coveredJetAmbientTorus U d y) : ℂ)‖ ≤
      allocatedFullGridNaturalVolume B U b S rowSets * η := by
  let N : ℂ := (allocatedFullGridNaturalVolume B U b S rowSets : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have hNnorm : ‖N‖ = allocatedFullGridNaturalVolume B U b S rowSets := by
    rw [Complex.norm_real, Real.norm_of_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le]
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedSupportedSlicedMaskedProfile_chart_mean B U b hR hσ S rowSets
      H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW f z hz,
      Complex.ofReal_mul, ← hFv, hgv z hz]
    have heq : allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
        ((gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) *
          (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)) -
        N * model (chart z) * (gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ) =
        N * (allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) -
          model (chart z)) * (gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ) := by
      unfold allocatedProductFullGridPrefactor
      let cv := allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z)
      let wv : ℂ := allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z)
      let gv : ℂ := gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1)
      change cv * (gv * wv) - N * model (chart z) * gv =
        N * (cv * (1 / N * wv) - model (chart z)) * gv
      field_simp
    rw [heq, norm_mul, norm_mul, hNnorm]
    have hg1 : ‖(gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ)‖ ≤ 1 := by
      rw [← hgv z hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgb _).1]
      exact (hgb _).2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (happrox _) (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le)
      hg1 (norm_nonneg _) (mul_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le hη)).trans_eq (mul_one _)
  · have hpzero (u) : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y = 0 := by
      unfold allocatedWholeMaskedCoveredProfile allocatedCoveredProfileDensity
      exact restrictedChartDensity_zero _ _ _ _ hy
    rw [← hFv, hzero y hy]
    simp only [hpzero, FiniteProbabilityWeights.mean_const, Complex.ofReal_zero,
      mul_zero, zero_mul, sub_self, norm_zero]
    exact mul_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le hη

end Erdos3.VectorPolynomial

end

end OAI
