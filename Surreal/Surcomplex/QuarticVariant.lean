import Surreal.Algebra.QuarticVariant
import Surreal.Foundations.OmnificQuartic
import Surreal.Surcomplex.DiophantineConstantsBoundary

/-!
# The alternative quartic on the actual omnific carriers

The real definition and Gaussian collapse in `odg:def:rem:quarticvariant`.
All real zeros have ordinary coordinates, whereas every Gaussian omnific
integer has the explicit witnesses printed in the source.
-/

universe u
namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

private theorem pell_mem_range (x y : OmnificInteger.{u})
    (h : x ^ 2 - 2 * y ^ 2 = 1) :
    x ∈ omnificIntCast.range ∧ y ∈ omnificIntCast.range := by
  have hp : x ^ 2 - omnificIntCast 2 * y ^ 2 = omnificIntCast 1 := by
    simpa only [map_ofNat, map_one] using h
  obtain ⟨hx, hy⟩ := Surcomplex.omnific_pell_rigidity 2 1 (by norm_num) (by norm_num) x y hp
  exact ⟨⟨omnificConstantCoeff x, hx.symm⟩, ⟨omnificConstantCoeff y, hy.symm⟩⟩

private theorem square_bound (z : OmnificInteger.{u}) (b : ℤ)
    (h : omnificToSurreal z ^ 2 ≤ omnificToSurreal (omnificIntCast b) ^ 2) :
    z ∈ omnificIntCast.range := by
  have hb : z ^ 2 ≤ omnificIntCast (b ^ 2) := by
    have h' : omnificToSurreal (z ^ 2) ≤ omnificToSurreal (omnificIntCast (b ^ 2)) := by
      simpa only [map_pow] using h
    exact h'
  obtain ⟨a, ha⟩ := omnific_standard_of_sq_le_int z (b ^ 2) hb
  exact ⟨a, ha.symm⟩

/-- Every real input and witness satisfying Source 07's quartic is ordinary. -/
theorem omnific_quarticVariant_witnesses (x r s : OmnificInteger.{u})
    (a : Fin 4 → OmnificInteger.{u}) (h : QuarticVariant.value x r s a = 0) :
    (∃ b : ℤ, x = omnificIntCast b) ∧ (∃ b : ℤ, r = omnificIntCast b) ∧
      (∃ b : ℤ, s = omnificIntCast b) ∧ (∀ j, ∃ b : ℤ, a j = omnificIntCast b) := by
  have hw := QuarticVariant.witnesses_mem_range omnificToSurreal omnificToSurreal_injective
    omnificIntCast pell_mem_range square_bound x r s a h
  simpa only [RingHom.mem_range, eq_comm] using hw

/-- The alternative quartic defines precisely the actual ordinary integer constants. -/
theorem omnific_quarticVariant_iff (x : OmnificInteger.{u}) :
    QuarticVariant.Defines x ↔ ∃ b : ℤ, x = omnificIntCast b := by
  rw [QuarticVariant.defines_iff_mem_range omnificToSurreal omnificToSurreal_injective
    omnificIntCast pell_mem_range square_bound]
  exact exists_congr (fun _ => eq_comm)

end Foundations.SignSequence

namespace Surcomplex

/-- The printed Gaussian witnesses work for every actual Gaussian omnific integer. -/
theorem gaussianOmnific_quarticVariant_witness (x : GaussianOmnificInteger.{u}) :
    QuarticVariant.value x 1 0
      ![gaussianOmnificConstants (⟨0, 1⟩ : GaussianInt) * x, 1, 0, 0] = 0 := by
  apply QuarticVariant.complex_collapse
  change gaussianOmnificConstants.{u} (⟨0, 1⟩ : GaussianInt) ^ 2 = -1
  rw [← map_pow, show (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 by decide, map_neg, map_one]

/-- Consequently the alternative quartic accepts the entire Gaussian omnific ring. -/
theorem gaussianOmnific_quarticVariant_all (x : GaussianOmnificInteger.{u}) :
    QuarticVariant.Defines x :=
  ⟨1, 0, _, gaussianOmnific_quarticVariant_witness x⟩

/-- In particular it accepts the nonconstant Conway monomial omega. -/
theorem gaussianOmnific_omega_quarticVariant_nonconstant :
    QuarticVariant.Defines (gaussianOmnificOmega.{u}) ∧
      ¬∃ a : GaussianInt, gaussianOmnificOmega.{u} = gaussianOmnificConstants a := by
  refine ⟨gaussianOmnific_quarticVariant_all _, ?_⟩
  rintro ⟨a, ha⟩
  have hc := congrArg gaussianOmnificConstantCoeff ha
  rw [gaussianOmnificOmega_constantCoeff, gaussianOmnificConstantCoeff_constants] at hc
  rw [← hc, map_zero] at ha
  exact gaussianOmnificOmega_ne_zero ha

end Surcomplex
end
end Surreal
