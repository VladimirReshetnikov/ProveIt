import GowersSzemeredi.Proofs16BohrFourTerm

/-! Complete the fourth row from three rows and a target parameter.
This is the local Bohr-domain form of the geometric implication in
reference [49], Claim 38; no quasirandomness is assumed or inferred. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A four-term relation and four quarter-radius phase bounds control the
missing row at full radius. -/
theorem varyingPattern_fourth_row {N m : Nat} [NeZero N]
    (T : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {rho eta : Real} (hrho : 0 ≤ rho)
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    {x₁ x₂ x₃ x₄ d : ZMod N}
    (h₁ : x₁ ∈ bohr T (rho / 4)) (h₂ : x₂ ∈ bohr T (rho / 4))
    (h₃ : x₃ ∈ bohr T (rho / 4)) (h₄ : x₄ ∈ bohr T (rho / 4))
    (hd₁ : d ∈ bohr (varyingPatternFrequencies psi J x₁) (eta / 4))
    (hd₂ : d ∈ bohr (varyingPatternFrequencies psi J x₂) (eta / 4))
    (hd₃ : d ∈ bohr (varyingPatternFrequencies psi J x₃) (eta / 4))
    (hdy : d ∈ bohr (varyingPatternFrequencies psi J (x₁ + x₂ - x₃ - x₄)) (eta / 4)) :
    d ∈ bohr (varyingPatternFrequencies psi J x₄) eta := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
  have hphase (t : ZMod N) (ht : d ∈ bohr (varyingPatternFrequencies psi J t) (eta / 4)) :
      (centeredAbs (psi i t * d) : Real) ≤ eta / 4 * N :=
    (Finset.mem_filter.mp ht).2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have heq := freiman_bohr_four_term T (psi i) hrho (hpsi i hi).1 (hpsi i hi).2 h₁ h₂ h₃ h₄
  have hmul : psi i x₄ * d = psi i x₁ * d + psi i x₂ * d - psi i x₃ * d -
      psi i (x₁ + x₂ - x₃ - x₄) * d := by rw [heq]; ring
  have hbound := centeredAbs_four_term_le (psi i x₁ * d) (psi i x₂ * d)
    (psi i x₃ * d) (psi i (x₁ + x₂ - x₃ - x₄) * d)
  rw [← hmul] at hbound
  linarith [hphase x₁ hd₁, hphase x₂ hd₂, hphase x₃ hd₃,
    hphase (x₁ + x₂ - x₃ - x₄) hdy]

/-- Three narrow rows and a narrow target imply four full rows, whose
vertical differences cancel the common anchor. -/
theorem recentered_four_row_completion {N m : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (W T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a : ZMod N)
    {rho eta : Real} (hrho : 0 ≤ rho) (heta : 0 ≤ eta)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    {x₁ x₂ x₃ x₄ d : ZMod N} (h₁ : x₁ ∈ W) (h₂ : x₂ ∈ W)
    (h₃ : x₃ ∈ W) (h₄ : x₄ ∈ W) (hc : d ∈ bohr F eta)
    (hd₁ : d ∈ bohr (varyingPatternFrequencies psi J x₁) (eta / 4))
    (hd₂ : d ∈ bohr (varyingPatternFrequencies psi J x₂) (eta / 4))
    (hd₃ : d ∈ bohr (varyingPatternFrequencies psi J x₃) (eta / 4))
    (hdy : d ∈ bohr (varyingPatternFrequencies psi J (x₁ + x₂ - x₃ - x₄)) (eta / 4)) :
    (d, x₁ + x₂ - x₃ - x₄) ∈ verDiff (verDiff A) := by
  have hd₄ := varyingPattern_fourth_row T psi J hrho hpsi
    (hW h₁) (hW h₂) (hW h₃) (hW h₄) hd₁ hd₂ hd₃ hdy
  have hA₁ := hgeom x₁ h₁ d hc (bohr_mono_radius _ (show eta / 4 ≤ eta by linarith) hd₁)
  have hA₂ := hgeom x₂ h₂ d hc (bohr_mono_radius _ (show eta / 4 ≤ eta by linarith) hd₂)
  have hA₃ := hgeom x₃ h₃ d hc (bohr_mono_radius _ (show eta / 4 ≤ eta by linarith) hd₃)
  have hA₄ := hgeom x₄ h₄ d hc hd₄
  have h := mem_verDiff (mem_verDiff hA₁ hA₃) (mem_verDiff hA₄ hA₂)
  simpa only [show (a + x₁ - (a + x₃)) - (a + x₄ - (a + x₂)) =
    x₁ + x₂ - x₃ - x₄ by ring] using h

/-- The triple-witness form used for the common-neighborhood argument. -/
theorem recentered_four_row_of_triple {N m : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (W T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a : ZMod N)
    {rho eta : Real} (hrho : 0 ≤ rho) (heta : 0 ≤ eta)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    {y d : ZMod N} (hc : d ∈ bohr F eta)
    (hdy : d ∈ bohr (varyingPatternFrequencies psi J y) (eta / 4))
    (hwitness : ∃ x₁ ∈ W, ∃ x₂ ∈ W, ∃ x₃ ∈ W, x₁ + x₂ - x₃ - y ∈ W ∧
      d ∈ bohr (varyingPatternFrequencies psi J x₁) (eta / 4) ∧
      d ∈ bohr (varyingPatternFrequencies psi J x₂) (eta / 4) ∧
      d ∈ bohr (varyingPatternFrequencies psi J x₃) (eta / 4)) :
    (d, y) ∈ verDiff (verDiff A) := by
  obtain ⟨x₁, h₁, x₂, h₂, x₃, h₃, h₄, hd₁, hd₂, hd₃⟩ := hwitness
  have heq : x₁ + x₂ - x₃ - (x₁ + x₂ - x₃ - y) = y := by ring
  have h := recentered_four_row_completion A W T F psi J a hrho heta hW hpsi hgeom
    h₁ h₂ h₃ h₄ hc hd₁ hd₂ hd₃ (by simpa only [heq] using hdy)
  simpa only [heq] using h

end LeanProofs.GowersSzemeredi
