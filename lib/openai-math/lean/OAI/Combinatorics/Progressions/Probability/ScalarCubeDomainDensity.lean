import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeDomain

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_volume_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume (scalarCubeDomain α) :=
  (scalarCubeDomain_isOpen α).measure_pos volume (scalarCubeDomain_nonempty α)

theorem scalarCubeDomain_volume_lt_top (α : Type*) [Fintype α] [DecidableEq α] :
    volume (scalarCubeDomain α) < ⊤ :=
  (measure_mono subset_closure).trans_lt (scalarCubeDomain_isBounded α).isCompact_closure.measure_lt_top

theorem scalarCubeDomain_volumeReal_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume.real (scalarCubeDomain α) :=
  ENNReal.toReal_pos (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

noncomputable def scalarCubeDomainDensity (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  (volume.real (scalarCubeDomain α))⁻¹

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

theorem scalarCubeDomainDensity_integrable (α : Type*) [Fintype α] [DecidableEq α] :
    IntegrableOn (fun _ : Option α → ℝ => scalarCubeDomainDensity α) (scalarCubeDomain α) :=
  integrableOn_const (scalarCubeDomain_volume_lt_top α).ne

theorem scalarCubeDomainDensity_mass (α : Type*) [Fintype α] [DecidableEq α] :
    (∫ _ in scalarCubeDomain α, scalarCubeDomainDensity α) = 1 := by
  rw [setIntegral_const, smul_eq_mul, scalarCubeDomainDensity]
  exact mul_inv_cancel₀ (scalarCubeDomain_volumeReal_pos α).ne'

end Erdos3

end

end OAI
