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
  by_cases hY : Y.Nonempty
  · have hshort : section10SymmetricMultiples d m ⊆ bohr K zeta := by
      by_cases hK : K.Nonempty
      · exact bohr_symmetric_multiples_subset K zeta
          (cor1014_small_bohr_nonnegative K zeta m hm d hd hK) m hm d hd
      · have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
        intro z _
        simp [bohr, hKempty]
    obtain ⟨a, ha⟩ := hY
    have hpsiZero : psi1 0 = 0 := by
      have hag := hagree a ha a ha
        (hshort (by simpa using cor1014_zero_mem_symmetric d m))
      simpa using hag.symm
    letI : Fact N.Prime := ⟨hprime⟩
    by_cases hd0 : d = 0
    · refine ⟨0, ?_⟩
      intro x hx y hy hxy
      have hdiff : D.index x - D.index y = 0 := by
        rw [section10SymmetricMultiples, Finset.mem_image] at hxy
        obtain ⟨j, _, hj⟩ := hxy
        simpa [hd0] using hj.symm
      simpa [hdiff, hpsiZero] using hagree x hx y hy (hshort hxy)
    · refine ⟨psi1 d / d, ?_⟩
      intro x hx y hy hxy
      have hag := hagree x hx y hy (hshort hxy)
      rw [section10SymmetricMultiples, Finset.mem_image] at hxy
      obtain ⟨j, hj, hjxy⟩ := hxy
      have hsame : symmetricMultiples d m = section10SymmetricMultiples d m := rfl
      have hdomain : symmetricMultiples d m ⊆ bohr K zeta := by
        simpa only [hsame] using hshort
      have hlin := freiman_map_int_multiple_of_zero (bohr K zeta) psi1 hpsi
        hpsiZero d m hm hdomain j hj
      rw [← hjxy, hlin] at hag
      rw [← hjxy]
      calc
        phi x - phi y = (j : ZMod N) * psi1 d := hag
        _ = (psi1 d / d) * ((j : ZMod N) * d) := by field_simp
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hY ⟨x, hx⟩).elim

end LeanProofs.GowersSzemeredi
