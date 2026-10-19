import GowersSzemeredi.Proofs07ProgressionLinearity
import GowersSzemeredi.Section10

/-!
# Scalar linearity for the multifunction Bohr model

This module proves Gowers's Corollary 10.14.  Its algebraic core is the
short-progression Freiman argument already used for Corollary 7.9; the only
additional work is deriving nonnegativity of the Bohr radius from the
existence of the smaller Bohr element.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] centeredAbs_neg

private lemma cor1014_small_bohr_nonnegative {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (zeta : Real) (m : Nat) (hm : 0 < m)
    (d : ZMod N) (hd : d ∈ bohr K (zeta / m)) (hK : K.Nonempty) :
    0 ≤ zeta := by
  obtain ⟨r, hr⟩ := hK
  rw [bohr, Finset.mem_filter] at hd
  have hbound := hd.2 r hr
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hNReal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  by_contra hzeta
  have hzetaNeg : zeta < 0 := lt_of_not_ge hzeta
  have hrhs : zeta / (m : Real) * N < 0 :=
    mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hzetaNeg hmReal) hNReal
  linarith

private lemma cor1014_zero_mem_symmetric {N : Nat} (d : ZMod N) (m : Nat) :
    (0 : ZMod N) ∈ section10SymmetricMultiples d m := by
  rw [section10SymmetricMultiples, Finset.mem_image]
  refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
  constructor <;> omega

/- **Gowers, Corollary 10.14.** -/
theorem corollary_10_14_holds : corollary_10_14 := by
  intro N _ X _ _ D phi K zeta Y psi1 hprime hmodel m hm d hd
  obtain ⟨hpsi, hagree⟩ := hmodel
  rcases Y.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  have hshort : section10SymmetricMultiples d m ⊆ bohr K zeta := by
    rcases K.eq_empty_or_nonempty with rfl | hK
    · intro z _
      simp [bohr]
    · exact bohr_symmetric_multiples_subset K zeta
        (cor1014_small_bohr_nonnegative K zeta m hm d hd hK) m hm d hd
  have hpsiZero : psi1 0 = 0 := by
    simpa using (hagree a ha a ha (hshort (by simpa using cor1014_zero_mem_symmetric d m))).symm
  letI : Fact N.Prime := ⟨hprime⟩
  refine ⟨psi1 d / d, fun x hx y hy hxy => ?_⟩
  obtain ⟨j, hj, hjxy⟩ := Finset.mem_image.mp hxy
  rw [hagree x hx y hy (hshort hxy), ← hjxy,
    freiman_map_int_multiple_of_zero _ psi1 hpsi hpsiZero d m hm hshort j hj]
  rcases eq_or_ne d 0 with rfl | hd0
  · simp [hpsiZero]
  · field_simp

end LeanProofs.GowersSzemeredi
