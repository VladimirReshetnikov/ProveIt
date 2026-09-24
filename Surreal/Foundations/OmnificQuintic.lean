import Surreal.Algebra.QuinticConstants
import Surreal.Surcomplex.DiophantineConstants

/-!
# The real quintic definition on the actual omnific integers

The actual-carrier instance of `odg:def:eq:quintic`: exactly the ordinary
integers have the seven witnesses in the actual omnific ring.
-/

universe u
namespace Surreal.Foundations.SignSequence

open QuinticConstants

noncomputable section

/-- The quintic defines precisely Z on the actual omnific carrier. -/
theorem omnific_quintic_iff (x : OmnificInteger.{u}) :
    Defines x ↔ ∃ a : ℤ, x = omnificIntCast a := by
  have hiff := defines_iff_mem_range omnificToSurreal omnificToSurreal_injective
    omnificIntCast (fun u v hp => ?_) (fun x w a ha he => ?_) integer_defines x
  · rw [hiff]
    exact exists_congr (fun a => eq_comm)
  · have hp' : u ^ 2 - omnificIntCast 2 * v ^ 2 = omnificIntCast 1 := by
      simpa only [map_ofNat, map_one] using hp
    have hv := (Surcomplex.omnific_pell_rigidity 2 1 (by norm_num) (by norm_num) u v hp').2
    exact ⟨omnificConstantCoeff v, hv.symm⟩
  · have ha0 : a ≠ 0 := by intro hz; apply ha; rw [hz, map_zero]
    obtain ⟨b, hb, _⟩ := (omnific_dvd_int_iff x a ha0).mp ⟨w, he.symm⟩
    exact ⟨b, hb.symm⟩

end
end Surreal.Foundations.SignSequence
