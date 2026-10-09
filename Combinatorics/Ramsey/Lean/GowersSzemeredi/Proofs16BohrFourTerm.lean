import GowersSzemeredi.Proofs16QuarterPatternGeometry

/-! Four-term identities with explicit control of every local domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_add_radius {N : Nat} [NeZero N] (T : Finset (ZMod N))
    {rho sigma : Real} {x y : ZMod N} (hx : x ∈ bohr T rho) (hy : y ∈ bohr T sigma) :
    x + y ∈ bohr T (rho + sigma) := by
  refine bohr_add_small T hy ?_
  simpa only [add_sub_cancel_right] using hx

theorem bohr_sub_radius {N : Nat} [NeZero N] (T : Finset (ZMod N))
    {rho sigma : Real} {x y : ZMod N} (hx : x ∈ bohr T rho) (hy : y ∈ bohr T sigma) :
    x - y ∈ bohr T (rho + sigma) := by
  simpa only [sub_eq_add_neg] using bohr_add_radius T hx (neg_mem_bohr hy)

theorem bohr_four_term_mem {N : Nat} [NeZero N] (T : Finset (ZMod N))
    {rho : Real} {x₁ x₂ x₃ x₄ : ZMod N}
    (h₁ : x₁ ∈ bohr T (rho / 4)) (h₂ : x₂ ∈ bohr T (rho / 4))
    (h₃ : x₃ ∈ bohr T (rho / 4)) (h₄ : x₄ ∈ bohr T (rho / 4)) :
    x₁ + x₂ - x₃ - x₄ ∈ bohr T rho := by
  have h := bohr_sub_radius T (bohr_add_radius T h₁ h₂) (bohr_add_radius T h₃ h₄)
  simpa only [show rho / 4 + rho / 4 + (rho / 4 + rho / 4) = rho by ring,
    sub_add_eq_sub_sub] using h

/-- The four-term identity only uses Freiman linearity inside the full
neighborhood; the four input points lie in the quarter neighborhood. -/
theorem freiman_bohr_four_term {N : Nat} [NeZero N] (T : Finset (ZMod N))
    (f : ZMod N → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hf : FreimanHom 2 (bohr T rho) f) (hf0 : f 0 = 0)
    {x₁ x₂ x₃ x₄ : ZMod N}
    (h₁ : x₁ ∈ bohr T (rho / 4)) (h₂ : x₂ ∈ bohr T (rho / 4))
    (h₃ : x₃ ∈ bohr T (rho / 4)) (h₄ : x₄ ∈ bohr T (rho / 4)) :
    f (x₁ + x₂ - x₃ - x₄) = f x₁ + f x₂ - f x₃ - f x₄ := by
  have hmono := bohr_mono_radius T (show rho / 4 ≤ rho by linarith)
  have h12 := bohr_mono_radius T (show rho / 4 + rho / 4 ≤ rho by linarith)
    (bohr_add_radius T h₁ h₂)
  have h34 := bohr_mono_radius T (show rho / 4 + rho / 4 ≤ rho by linarith)
    (bohr_add_radius T h₃ h₄)
  have hlin := hf.isFreimanLinearOn (by decide)
  have hzero := zero_mem_bohr T hrho
  have hs12 := hlin x₁ x₂ (x₁ + x₂) 0 (hmono h₁) (hmono h₂) h12 hzero (by ring)
  have hs34 := hlin x₃ x₄ (x₃ + x₄) 0 (hmono h₃) (hmono h₄) h34 hzero (by ring)
  have hmain := hlin (x₁ + x₂ - x₃ - x₄) (x₃ + x₄) (x₁ + x₂) 0
    (bohr_four_term_mem T h₁ h₂ h₃ h₄) h34 h12 hzero (by ring)
  rw [hf0] at hs12 hs34 hmain
  linear_combination hmain - hs12 + hs34

/-- Four phase errors add, including both negative terms. -/
theorem centeredAbs_four_term_le {N : Nat} [NeZero N] (a b c d : ZMod N) :
    (centeredAbs (a + b - c - d) : Real) ≤
      centeredAbs a + centeredAbs b + centeredAbs c + centeredAbs d := by
  have h1 := centeredAbs_add_le a b
  have h2 := centeredAbs_add_le (a + b) (-c)
  have h3 := centeredAbs_add_le (a + b + -c) (-d)
  simp only [centeredAbs_neg, ← sub_eq_add_neg] at h2 h3
  exact_mod_cast (show centeredAbs (a + b - c - d) ≤
    centeredAbs a + centeredAbs b + centeredAbs c + centeredAbs d by omega)

end LeanProofs.GowersSzemeredi
