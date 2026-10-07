import OAI.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedCoveredChart_of_integer_deck
    (M : ℕ) [NeZero M] (u : W) (x : W × (Fin n → ℤ)) (deck : E → ℤ)
    (hdeck : normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm deck).val = u) :
    (QuotientAddGroup.mk ((M : ℝ)⁻¹ • u) : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW M (x, integerResidueMap E M deck) := by
  have h := normalizedCoverLift_add_deck W bW b hb M (NeZero.pos M) x deck
  rw [hdeck] at h
  exact h.symm

theorem exists_forecast_individual_cover_transport
    (d : ℕ) [NeZero d] (u : W) (x : W × (Fin n → ℤ)) (r : E → ZMod d)
    (hchart : (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u) : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW d (x, r)) :
    ∃ deck : E → ℤ,
      normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm deck).val = u ∧
      integerResidueMap E d deck = r ∧
      ∀ (M : ℕ) [NeZero M],
        (QuotientAddGroup.mk ((M : ℝ)⁻¹ • u) : W ⧸
          (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
            normalizedCoveredChart W b hb bW M (x, integerResidueMap E M deck) := by
  obtain ⟨deck, hdeck, hr⟩ := exists_covered_representative_offset W bW b hb d
    ((d : ℝ)⁻¹ • u) x r hchart
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hdeck
  exact ⟨deck, hdeck, hr, fun M _ =>
    normalizedCoveredChart_of_integer_deck W bW b hb M u x deck hdeck⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "single" => (fun _ : Fin m => Unit)

include B S in
theorem exists_forecast_physical_quarter_recovery
    (r : ℝ≥0) (hr : 0 < r)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j e, coefficients (p j) e ∈ U j) (t : X → ℝ)
    (hnonzero : allocatedBufferedTorusCutoff (R := R) U b o r hr
      (fun a : JetAmbientIndex single J => (eval t (p a.1) a.2.2 : UnitAddCircle)) ≠ 0) :
    ∃ (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ),
      (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j) ∧
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) := by
  let y := BooleanCubeKernel.physicalSingleSiteValue U 1 p hp t
  let chart := mixedCoveredJetChart (O := single) U o b hb bW 1
  let region := mixedCoveredJetRegion (O := single) (E := E) U o b 1
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
  have hcut := allocatedBufferedTorusCutoff_eq_siteChart U b o r hr hR C hC hchart hbudget
    B S hb bW 1 y
  rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at hcut
  have hsite : allocatedBufferedSiteChartFactor B U b S o hb bW 1 r hr (fun _ => 1) y ≠ 0 := by
    rw [← hcut]
    exact_mod_cast hnonzero
  have hy : y ∈ chart '' region := by
    by_contra hnot
    exact hsite (restrictedComplexChartDensity_zero _ _ _ _ hnot)
  obtain ⟨z, hz, he⟩ := hy
  let w := fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit (z.1 j) ()
  have hquarter (j : Fin m) (i : J j) :
      |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4 :=
    (hz j (mem_univ j) () (mem_univ ())).1 i
  have hcovered (j : Fin m) :
      (QuotientAddGroup.mk (((1 : ℕ) : ℝ)⁻¹ • BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j) :
        euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) 1
        (orthonormalMixedChart (o j) (w j), z.2 j ()) := by
    exact (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hp 1 t j).symm.trans
      (congrFun (congrFun he j) ()).symm
  have hlift (j : Fin m) : ∃ deck : E j → ℤ,
      normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
        (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm deck).val =
      BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j := by
    obtain ⟨deck, hdeck, _⟩ := exists_forecast_individual_cover_transport
      (euclideanSubspace (U j)) (bW j) (b j) (hb j) 1
      (BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j)
      (orthonormalMixedChart (o j) (w j)) (z.2 j ()) (hcovered j)
    exact ⟨deck, hdeck⟩
  choose deck hdeck using hlift
  exact ⟨w, deck, hdeck, hquarter⟩

end Erdos3.VectorPolynomial

end

end OAI
