import OAI.Combinatorics.Progressions.Fourier.IntegerPeriodicTorusLift
import OAI.Combinatorics.Progressions.Lattices.LatticeDualCoordinates
import OAI.Combinatorics.Progressions.Lattices.LatticeGaussianCoefficient
import OAI.Combinatorics.Progressions.Lattices.LatticeSheetHaar

namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeBasis_integerCoordinates (b : Module.Basis ι ℤ Λ) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => (n i : ℝ)) = (b.equivFun.symm n : E) := by
  apply (b.ofZLatticeBasis ℝ Λ).equivFun.injective
  ext i
  rw [LinearEquiv.apply_symm_apply]
  change (n i : ℝ) = (b.ofZLatticeBasis ℝ Λ).repr (b.equivFun.symm n : E) i
  rw [Module.Basis.ofZLatticeBasis_repr_apply]
  exact (congrArg (fun z : ℤ => (z : ℝ)) (congrFun (b.equivFun.apply_symm_apply n) i)).symm

theorem latticeGaussian_integer_periodic (b : Module.Basis ι ℤ Λ) (t : ℝ)
    (x : ι → ℝ) (n : ι → ℤ) :
    latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => x i + (n i : ℝ))) =
      latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) := by
  change latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (x + (fun i => (n i : ℝ)))) = _
  rw [map_add, latticeBasis_integerCoordinates]
  exact latticeGaussianMass_add_lattice Λ t _ _

noncomputable def latticeGaussianTorus (b : Module.Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) :
    C(UnitAddTorus ι, ℂ) where
  toFun := integerPeriodicTorusLift (fun x =>
    (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) : ℂ))
  continuous_toFun := continuous_integerPeriodicTorusLift _
    (Complex.continuous_ofReal.comp ((continuous_latticeGaussianMass Λ ht).comp
      (b.ofZLatticeBasis ℝ Λ).equivFunL.symm.continuous))
    (fun x n => congrArg (fun z : ℝ => (z : ℂ)) (latticeGaussian_integer_periodic Λ b t x n))

theorem latticeGaussianTorus_coe (b : Module.Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t)
    (x : ι → ℝ) :
    latticeGaussianTorus Λ b ht (fun i => (x i : UnitAddCircle)) =
      (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) : ℂ) :=
  integerPeriodicTorusLift_coe (fun y =>
    (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm y) : ℂ))
    (fun y n => congrArg (fun z : ℝ => (z : ℂ)) (latticeGaussian_integer_periodic Λ b t y n)) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianTorus_coefficient (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) (n : ι → ℤ) :
    (ZLattice.covolume Λ : ℂ) * UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
      ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
        Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℝ) : ℂ) := by
  classical
  let bR := b.ofZLatticeBasis ℝ Λ
  let f : E → ℂ := fun x => euclideanCharacter (-latticeDualPoint Λ b n) x *
    (latticeGaussianMass Λ t x : ℂ)
  have hsets : Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) =ᵐ[volume]
      Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) :=
    (Measure.ae_eq_set_pi (μ := fun _ : ι => (volume : Measure ℝ))
      (fun _ _ => Ico_ae_eq_Ioc)).symm
  have hcoeff : UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
      ∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1), f (bR.equivFun.symm x) := by
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => 0)]
    simp only [zero_add, smul_eq_mul]
    have he : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) := by ext; simp
    rw [he, setIntegral_congr_set hsets]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [latticeGaussianTorus_coe, ← latticeDualPoint_character Λ b (-n) x, latticeDualPoint_neg]
  rw [hcoeff, latticeBasis_integral_cube]
  exact latticeGaussian_integral_character Λ (ZSpan.fundamentalDomain bR)
    (ZSpan.fundamentalDomain_measurableSet bR) (ZSpan.fundamentalDomain_isBounded bR)
    (ZLattice.isAddFundamentalDomain b volume) ht _ (latticeDualPoint_mem Λ b n)

end Erdos3

end

end OAI
