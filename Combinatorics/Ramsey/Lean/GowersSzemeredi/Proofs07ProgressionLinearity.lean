import GowersSzemeredi.Proofs07BohrHom

/-!
# Linearity of the induced map on short progressions

This module proves Gowers's Corollary 7.9.  Lemma 7.8 supplies a Freiman
homomorphism on a Bohr neighborhood.  Repeated addition then makes that map
linear on every sufficiently short symmetric progression; primality of the
modulus lets us express the resulting coefficient as an ambient scalar.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] centeredAbs_neg

/-- A Freiman map that vanishes at zero agrees with integer scalar
multiplication throughout a symmetric progression contained in its domain. -/
lemma freiman_map_int_multiple_of_zero {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (psi : ZMod N → ZMod N)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod N) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (j : Int)
    (hj : j ∈ Finset.Icc (-(m : Int)) (m : Int)) :
    psi ((j : ZMod N) * d) = (j : ZMod N) * psi d :=
  (generic_freiman_map_int_multiple B psi hpsi hpsiZero d m hm hmem j hj).trans
    (zsmul_eq_mul _ _)

/- **Gowers, Corollary 7.9.** -/
theorem corollary_7_9_holds : corollary_7_9 := by
  intro N _ A phi alpha hprime halpha hcard hphi
  dsimp only
  intro m hm d hd
  obtain ⟨_, hBhom⟩ := lemma_7_8_holds N A phi alpha halpha hcard hphi
  obtain ⟨psi, hpsi, hagree⟩ := hBhom
  let K := section7Spectrum A alpha
  let B := bohr K (alpha / (32 * Real.pi))
  have hshort : symmetricMultiples d m ⊆ B :=
    bohr_symmetric_multiples_subset K (alpha / (32 * Real.pi)) (by positivity) m hm d
      (by rwa [div_div])
  have hzeroShort : (0 : ZMod N) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hNpos : 0 < N := NeZero.pos N
  have hAcard : 0 < A.card := by
    have : (0 : Real) < A.card := by rw [hcard]; positivity
    exact_mod_cast this
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hAcard
  have hpsiZero : psi 0 = 0 := by
    have hag := hagree a ha a ha (hshort (by simpa using hzeroShort))
    simpa using hag.symm
  letI : Fact N.Prime := ⟨hprime⟩
  by_cases hd0 : d = 0
  · refine ⟨0, ?_⟩
    intro x hx y hy hxy
    have hdiff : x - y = 0 := by
      rw [symmetricMultiples, Finset.mem_image] at hxy
      obtain ⟨j, _, hj⟩ := hxy
      simpa [hd0] using hj.symm
    simpa [hdiff, hpsiZero] using hagree x hx y hy (hshort hxy)
  · refine ⟨psi d / d, ?_⟩
    intro x hx y hy hxy
    have hag := hagree x hx y hy (hshort hxy)
    rw [symmetricMultiples, Finset.mem_image] at hxy
    obtain ⟨j, hj, hjxy⟩ := hxy
    have hlin := freiman_map_int_multiple_of_zero B psi hpsi hpsiZero d m hm hshort j hj
    rw [← hjxy, hlin] at hag
    rw [← hjxy]
    calc
      phi x - phi y = (j : ZMod N) * psi d := hag
      _ = (psi d / d) * ((j : ZMod N) * d) := by
        field_simp

end LeanProofs.GowersSzemeredi
