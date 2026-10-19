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
  obtain ⟨-, psi, hpsi, hagree⟩ := lemma_7_8_holds N A phi alpha halpha hcard hphi
  have hshort := bohr_symmetric_multiples_subset (section7Spectrum A alpha)
    (alpha / (32 * Real.pi)) (by positivity) m hm d (by rwa [div_div])
  have hA : (0 : Real) < A.card := by
    rw [hcard]; exact mul_pos halpha (Nat.cast_pos.mpr (NeZero.pos N))
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hA)
  have hpsiZero : psi 0 = 0 := by
    simpa using (hagree a ha a ha (hshort (Finset.mem_image.mpr ⟨0, by simp, by simp⟩))).symm
  letI : Fact N.Prime := ⟨hprime⟩
  refine ⟨psi d / d, fun x hx y hy hxy => ?_⟩
  obtain ⟨j, hj, hjxy⟩ := Finset.mem_image.mp hxy
  rw [hagree x hx y hy (hshort hxy), ← hjxy,
    freiman_map_int_multiple_of_zero _ psi hpsi hpsiZero d m hm hshort j hj]
  rcases eq_or_ne d 0 with rfl | hd0
  · simp [hpsiZero]
  · field_simp

end LeanProofs.GowersSzemeredi
