import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import OAI.Combinatorics.Progressions.Estimates.MinkowskiSecondInduction
import OAI.Combinatorics.Progressions.Lattices.FiniteLatticeBasis
import OAI.Combinatorics.Progressions.Linear.BasisImageSection
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def integerCoordinateLattice : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

instance integerCoordinateLattice_discrete :
    DiscreteTopology (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

instance integerCoordinateLattice_full : IsZLattice ℝ (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

theorem mem_integerCoordinateLattice_iff (x : ι → ℝ) :
    x ∈ integerCoordinateLattice ↔ x ∈ realIntegerGrid := by
  change x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      simpa using hx i
    choose z hz using h
    exact ⟨z, funext hz⟩
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, by simpa using congrFun hz i⟩

theorem integerCoordinateLattice_covolume :
    ZLattice.covolume (integerCoordinateLattice (ι := ι)) = 1 := by
  change ZLattice.covolume (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) = 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume), measureReal_def]
  have hv : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]
  rw [hv]
  simp

theorem integer_lattice_covolume_eq_index
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    ZLattice.covolume L = L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex L integerCoordinateLattice hL
  simpa only [integerCoordinateLattice_covolume, div_one] using h

theorem integer_lattice_index_pos
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    0 < L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_pos L volume
  rw [integer_lattice_covolume_eq_index L hL] at h
  exact_mod_cast h

theorem integer_lattice_index_nsmul_mem (L : Submodule ℤ (ι → ℝ))
    (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup • x ∈ L :=
  L.toAddSubgroup.nsmul_relIndex_mem ((mem_integerCoordinateLattice_iff x).mpr hx)

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι : Type*}

def integerVectorRealMap : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem integerVectorRealMap_injective :
    Function.Injective (integerVectorRealMap (ι := ι)) := by
  intro x y h
  ext i
  exact Int.cast_injective (congrFun h i)

variable [Fintype ι] {N : ℕ}

noncomputable def integerVectorRealEquiv :
    (ι → ℤ) ≃ₗ[ℤ] (integerCoordinateLattice (ι := ι)) :=
  LinearEquiv.ofBijective
    (integerVectorRealMap.codRestrict integerCoordinateLattice (fun x =>
      (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩))
    ⟨fun _ _ h => integerVectorRealMap_injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := (mem_integerCoordinateLattice_iff _).mp y.property
      exact ⟨x, Subtype.ext hx⟩⟩

def cyclicIntegerKernel (η : (ι → ℤ) →+ ZMod N) : Submodule ℤ (ι → ℝ) :=
  (LinearMap.ker η.toIntLinearMap).map integerVectorRealMap

omit [Fintype ι] in
theorem mem_cyclicIntegerKernel (η : (ι → ℤ) →+ ZMod N) (y : ι → ℝ) :
    y ∈ cyclicIntegerKernel η ↔ ∃ x : ι → ℤ, η x = 0 ∧ integerVectorRealMap x = y :=
  Iff.rfl

omit [Fintype ι] in
theorem integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    integerVectorRealMap x ∈ cyclicIntegerKernel η ↔ η x = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact integerVectorRealMap_injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem cyclicIntegerKernel_le_integerCoordinateLattice
    (η : (ι → ℤ) →+ ZMod N) : cyclicIntegerKernel η ≤ integerCoordinateLattice := by
  rintro y ⟨x, _, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩

instance cyclicIntegerKernel_discrete (η : (ι → ℤ) →+ ZMod N) :
    DiscreteTopology (cyclicIntegerKernel η) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff _).mp
    (cyclicIntegerKernel_le_integerCoordinateLattice η hy)

omit [Fintype ι] in
theorem nsmul_integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    N • integerVectorRealMap x ∈ cyclicIntegerKernel η := by
  rw [← map_nsmul, integerVectorRealMap_mem_cyclicIntegerKernel, map_nsmul]
  simp [nsmul_eq_mul]

instance cyclicIntegerKernel_full [NeZero N] (η : (ι → ℤ) →+ ZMod N) :
    IsZLattice ℝ (cyclicIntegerKernel η) := by
  classical
  constructor
  apply top_unique
  rw [← (Pi.basisFun ℝ ι).span_eq]
  apply Submodule.span_le.mpr
  rintro y ⟨i, rfl⟩
  have hmem := nsmul_integerVectorRealMap_mem_cyclicIntegerKernel η (Pi.single i 1)
  have hcast : integerVectorRealMap (Pi.single i (1 : ℤ)) = Pi.basisFun ℝ ι i := by
    ext j
    simp [integerVectorRealMap, Pi.basisFun_apply, Pi.single_apply]
  rw [hcast] at hmem
  have hmemR : (N : ℝ) • Pi.basisFun ℝ ι i ∈ cyclicIntegerKernel η := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hmem
  have hspan : (N : ℝ) • Pi.basisFun ℝ ι i ∈
      Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ)) := Submodule.subset_span hmemR
  have hscale := (Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ))).smul_mem
    ((N : ℝ)⁻¹) hspan
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [smul_smul, inv_mul_cancel₀ hN, one_smul] at hscale
  exact hscale

theorem cyclicIntegerKernel_covolume_eq_card_range [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) = (Nat.card η.range : ℝ) := by
  classical
  rw [integer_lattice_covolume_eq_index _ (cyclicIntegerKernel_le_integerCoordinateLattice η)]
  have hindex : (cyclicIntegerKernel η).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup = Nat.card η.range := by
    let e := (integerVectorRealEquiv (ι := ι)).toAddEquiv.toAddMonoidHom
    let H := (cyclicIntegerKernel η).toAddSubgroup.addSubgroupOf
      (integerCoordinateLattice (ι := ι)).toAddSubgroup
    have he : H.comap e = η.ker := by
      ext x
      exact integerVectorRealMap_mem_cyclicIntegerKernel η x
    change H.index = Nat.card η.range
    rw [← H.index_comap_of_surjective (f := e) (integerVectorRealEquiv (ι := ι)).surjective,
      he, AddSubgroup.index_ker]
  exact_mod_cast hindex

theorem cyclicIntegerKernel_covolume_le [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) ≤ (N : ℝ) := by
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  have h := Nat.card_le_card_of_injective (fun x : η.range => (x : ZMod N))
    Subtype.val_injective
  have hcard : Nat.card (ZMod N) = N := by simp
  rw [hcard] at h
  exact_mod_cast h

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImage : Submodule ℤ (ι → ℝ) := Λ.map (π.restrictScalars ℤ)

theorem latticeImage_le_integer (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    latticeImage Λ π ≤ integerCoordinateLattice := by
  rintro y ⟨x, hx, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr (hπ x hx)

theorem latticeImage_discrete (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    DiscreteTopology (latticeImage Λ π) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff y).mp (latticeImage_le_integer Λ π hπ hy)

theorem latticeImage_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (latticeImage Λ π)] (hπ : Function.Surjective π) :
    IsZLattice ℝ (latticeImage Λ π) := by
  constructor
  change Submodule.span ℝ (π '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hπ

theorem latticeImage_index_lift (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    ∃ y ∈ Λ, π y = (latticeImage Λ π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup • x := by
  exact integer_lattice_index_nsmul_mem (latticeImage Λ π) x hx

theorem latticeImage_index_pos [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    0 < (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  let : DiscreteTopology (latticeImage Λ π) := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ (latticeImage Λ π) := latticeImage_full Λ π hsurj
  exact integer_lattice_index_pos (latticeImage Λ π) (latticeImage_le_integer Λ π hinteger)

end Erdos3

end

section

namespace Erdos3

open Module BohrLattice.MinkowskiDiagonalNormalization
open scoped BigOperators Matrix

theorem lattice_basis_coordinates_bound
    {r : ℕ} (Λ : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin r) ℤ Λ) (ρ : Fin r → ℝ) (hρ : ∀ j, 0 < ρ j)
    {H : ℝ} (hH : 0 ≤ H) (hb : ∀ i j, |(b i : Fin r → ℝ) j| ≤ H * ρ j)
    (hcov : (∏ j, ρ j) ≤ ZLattice.covolume Λ)
    (x : Fin r → ℝ) (hx : ∀ j, |x j| ≤ ρ j) (i : Fin r) :
    |(b.ofZLatticeBasis ℝ Λ).equivFun x i| ≤
      (r : ℝ) * r.factorial * H ^ (r - 1) := by
  classical
  let B := b.ofZLatticeBasis ℝ Λ
  let M : Matrix (Fin r) (Fin r) ℝ := fun i j => B j i / ρ i
  have hM : M = (Matrix.of (normalizedBasis B ρ hρ))ᵀ := by
    ext i j
    simp [M]
  have hB : |(Matrix.of B).det| = ZLattice.covolume Λ := by
    have he : (B : Fin r → Fin r → ℝ) = fun j => (b j : Fin r → ℝ) :=
      funext (fun j => Basis.ofZLatticeBasis_apply ℝ Λ b j)
    rw [he]
    exact (ZLattice.covolume_eq_det Λ b).symm
  have hprod : 0 < ∏ j, ρ j := Finset.prod_pos (fun j _ => hρ j)
  have hdet : 1 ≤ |M.det| := by
    rw [hM, Matrix.det_transpose, abs_det_normalizedBasis, hB, ← div_eq_mul_inv]
    exact (le_div_iff₀ hprod).mpr (by simpa using hcov)
  have hentry : ∀ j k, |M j k| ≤ H := by
    intro j k
    change |B k j / ρ j| ≤ H
    rw [abs_div, abs_of_pos (hρ j)]
    apply (div_le_iff₀ (hρ j)).mpr
    simpa only [B, Basis.ofZLatticeBasis_apply] using hb k j
  have hinv : ∀ j k, |M⁻¹ j k| ≤ (r.factorial : ℝ) * H ^ (r - 1) := by
    intro j k
    simpa only [Fintype.card_fin, div_one] using
      matrix_inverse_entry_abs_le M hentry (by norm_num : (0 : ℝ) < 1) hdet j k
  have hMx : M.mulVec (B.equivFun x) = fun j => x j / ρ j := by
    exact basis_coordinate_matrix_mulVec B (divideCoordinates ρ hρ).toLinearMap x
  have hback : M⁻¹.mulVec (fun j => x j / ρ j) = B.equivFun x := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (abs_pos.mp (lt_of_lt_of_le zero_lt_one hdet))), Matrix.one_mulVec]
  have hsmall (j) : |x j / ρ j| ≤ 1 := by
    rw [abs_div, abs_of_pos (hρ j)]
    exact (div_le_one (hρ j)).mpr (hx j)
  change |B.equivFun x i| ≤ _
  rw [← hback]
  change |∑ j, M⁻¹ i j * (x j / ρ j)| ≤ _
  calc
    _ ≤ ∑ j, |M⁻¹ i j * (x j / ρ j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin r, (r.factorial : ℝ) * H ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have h := mul_le_mul (hinv i j) (hsmall j) (abs_nonneg _) (by positivity)
      simpa only [mul_one] using h
    _ = _ := by simp [mul_assoc]

end Erdos3

end

section

namespace Erdos3

theorem basisFun_mem_realIntegerGrid {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Pi.basisFun ℝ ι i ∈ realIntegerGrid := by
  refine ⟨Pi.single i (1 : ℤ), ?_⟩
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply]

theorem latticeImage_basis_lifts {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) :
    let I := (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup
    ∀ i, ∃ x ∈ Λ, π x = (I : ℝ) • Pi.basisFun ℝ ι i := by
  intro I i
  obtain ⟨x, hx, hπx⟩ := latticeImage_index_lift Λ π (Pi.basisFun ℝ ι i)
    (basisFun_mem_realIntegerGrid i)
  refine ⟨x, hx, ?_⟩
  simpa only [Nat.cast_smul_eq_nsmul] using hπx

end Erdos3

end

end OAI
