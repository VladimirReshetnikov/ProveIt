import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedFiniteIdealInputLog {A : Type*} [Semiring A] (m : ℕ) (D eδ eε : A) : A :=
  (8 * allocatedIdealCoverInputLog m D 0 + 14) + 2 * D + 2 + eδ + eε

theorem allocatedFiniteIdealInputLog_bounds (m : ℕ) {D eδ eε : ℝ}
    (hD : 0 ≤ D) (hδ : 0 ≤ eδ) (hε : 0 ≤ eε) :
    let p := allocatedFiniteIdealInputLog m D eδ eε
    0 ≤ p ∧ (8 * allocatedIdealCoverInputLog m D 0 + 14) + 2 * D + 2 ≤ p ∧
      eδ ≤ p ∧ eε ≤ p := by
  have hbase := (allocatedProductChartLog_bounds m hD (le_refl (0 : ℝ))).2.1
  dsimp only [allocatedFiniteIdealInputLog]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)

variable {Dgeom cgeom : ℝ}
variable (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim)
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type)) Dgeom)
variable (hcgeom : 0 ≤ cgeom)
variable (hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom) (hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hCgeom : ∀ j, C j ≤ Real.exp cgeom)
variable (hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)

include hR hM hx hgeom hcgeom hIgeom hngeom hC hchart hCgeom hsmall in
theorem exists_good_kernel_finite_ideal_family (hdim : dim ≤ m + 1)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε eδ eε : ℝ}
    (hε : 0 < ε) (heδ : 0 ≤ eδ) (heε : 0 ≤ eε)
    (hδexp : (δ : ℝ)⁻¹ ≤ Real.exp eδ) (hεexp : ε⁻¹ ≤ Real.exp eε) :
    ∃ t : Fin M,
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (kernelPeriodCandidate (m + 1) t : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (rowTypes j) (kernelPeriodCandidate (m + 1) t : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ q : ℕ, ∃ F : tuples → AllocatedFiniteIdealData (Fin dim) I n,
        ∀ y₀, (F y₀).Bounds B U b S rowSets x y₀ q d (kernelPeriodCandidate (m + 1) t)
          hb o bW hR δ ε (allocatedFiniteIdealInputLog m Dgeom eδ eε) (layerKernelIndexBound m M) := by
  have hrows : ∀ j (s : rowTypes j), s.val.card ≤ j.val + 1 :=
    fun j s => (mem_boundedBooleanJetRows (j.val + 1) s.val).mp s.property
  obtain ⟨t, hspatial, hperiod⟩ := goodKernel_periodFamily selection x hx (m + 1) (by omega)
    (fun j : Fin m => j.val + 1) (fun j => by omega) rows (fun _ => Subtype.val_injective) hrows
  refine ⟨t, hspatial, hperiod, ?_⟩
  intro q
  obtain ⟨hp, hboxP, hδP, hεP⟩ := allocatedFiniteIdealInputLog_bounds m hgeom.nonneg heδ heε
  have hbox := allocatedProductIdealSiteRadius_exp_bound B rowSets hgeom (le_refl (0 : ℝ))
    hIgeom hngeom (fun _ => 0) (fun _ => le_rfl) (fun _ => (Real.exp_pos 0).le)
  have hbudget := allocatedProductChartRadius_recovery_budget B rowSets hgeom hcgeom
    hIgeom hngeom C hC hCgeom (fun j => (hR j).le) hsmall
  have hmaskOne : (1 : ℝ) ≤ layerKernelIndexBound m M := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  have hlocal (y₀ : tuples) : ∃ F : AllocatedFiniteIdealData (Fin dim) I n,
      F.Bounds B U b S rowSets x y₀ q d (kernelPeriodCandidate (m + 1) t)
        hb o bW hR δ ε (allocatedFiniteIdealInputLog m Dgeom eδ eε) (layerKernelIndexBound m M) := by
    apply exists_allocated_finite_ideal_data B U b S rowSets x y₀ q d
      (kernelPeriodCandidate (m + 1) t) hb o bW hR hperiod hmaskOne
      (fun j z => allocatedIntegerKernelMask_bound B U b S x rows hM selection hx
        (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hrows j q _ z)
      C hC hchart hbudget δ hδ hδ1 hε hp
      (hbox.trans (Real.exp_le_exp.mpr hboxP))
      (hεexp.trans (Real.exp_le_exp.mpr hεP)) (hδexp.trans (Real.exp_le_exp.mpr hδP))
  choose F hF using hlocal
  exact ⟨F, hF⟩

end Erdos3.VectorPolynomial

end

end OAI
