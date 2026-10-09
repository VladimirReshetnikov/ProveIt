import GowersSzemeredi.Proofs16PatternBohrDegrees
import GowersSzemeredi.Proofs16WeightedBohrFilling

/-! A single typical degree gives a quantitative positive graph density,
using the explicit Bohr cardinality lower bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem pattern_degree_card_lower {N m Q r : Nat} [NeZero N] [NeZero Q]
    (F : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta : Real} (heta : 0 ≤ eta) (t : ZMod N)
    (hK : (F ∪ varyingPatternFrequencies psi J t).card ≤ r) (hQ : 4 ≤ eta * Q) :
    (N : Real) ≤ (Q : Real)^r * (patternDegreeBohr F psi J eta t).card := by
  have hsub : bohr (F ∪ varyingPatternFrequencies psi J t) (eta / 4) ⊆
      patternDegreeBohr F psi J eta t := by
    rw [bohr_union, patternDegreeBohr_eq_inter F psi J heta t]
    intro x hx
    exact Finset.mem_inter.mpr ⟨bohr_mono_radius F (by linarith) (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  have hlow : (N : Real) ≤ (Q : Real)^(F ∪ varyingPatternFrequencies psi J t).card *
      (bohr (F ∪ varyingPatternFrequencies psi J t) (eta / 4)).card := by
    exact_mod_cast bohr_card_lower (F ∪ varyingPatternFrequencies psi J t) Q
      (show 1 ≤ eta / 4 * Q by linarith)
  have hpow : (Q : Real)^(F ∪ varyingPatternFrequencies psi J t).card ≤ (Q : Real)^r := by
    exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hK
  have hcard : ((bohr (F ∪ varyingPatternFrequencies psi J t) (eta / 4)).card : Real) ≤
      (patternDegreeBohr F psi J eta t).card := by exact_mod_cast Finset.card_le_card hsub
  exact hlow.trans (mul_le_mul hpow hcard (by positivity) (by positivity))

/-- The approximating density cannot be arbitrarily small when even one
vertex has a controlled degree. -/
theorem pattern_density_lower_of_degree {N m Q r : Nat} [NeZero N] [NeZero Q]
    (F : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta delta e : Real}
    (heta : 0 ≤ eta) (hd : 0 ≤ delta) (he : 0 ≤ e) (t : ZMod N)
    (hK : (F ∪ varyingPatternFrequencies psi J t).card ≤ r) (hQ : 4 ≤ eta * Q)
    (hdeg : |(patternDegreeBohr F psi J eta t).card - delta * ((bohr F eta).card : Real)| ≤
      e * (bohr F eta).card) :
    1 / (Q : Real)^r - e ≤ delta := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQpow : (0 : Real) < (Q : Real)^r := by
    have : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
    positivity
  have hB : ((bohr F eta).card : Real) ≤ N := by
    exact_mod_cast (show (bohr F eta).card ≤ N by simpa using Finset.card_le_univ (bohr F eta))
  have hD : ((patternDegreeBohr F psi J eta t).card : Real) ≤ (delta + e) * N := by
    have h := (abs_le.mp hdeg).2
    have hs := mul_le_mul_of_nonneg_left hB (add_nonneg hd he)
    nlinarith only [h, hs]
  have hlow := pattern_degree_card_lower F psi J heta t hK hQ
  have hscaled := hlow.trans (mul_le_mul_of_nonneg_left hD hQpow.le)
  have hone : 1 ≤ (Q : Real)^r * (delta + e) :=
    (mul_le_mul_iff_left₀ hN).mp (by nlinarith only [hscaled])
  have := (div_le_iff₀ hQpow).mpr (show 1 ≤ (delta + e) * (Q : Real)^r by nlinarith only [hone])
  linarith

/-- A small degree error supplies the strict positivity needed by row filling. -/
theorem pattern_density_pos_of_degree {N m Q r : Nat} [NeZero N] [NeZero Q]
    (F : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta delta e : Real}
    (heta : 0 ≤ eta) (hd : 0 ≤ delta) (he : 0 ≤ e) (t : ZMod N)
    (hK : (F ∪ varyingPatternFrequencies psi J t).card ≤ r) (hQ : 4 ≤ eta * Q)
    (hdeg : |(patternDegreeBohr F psi J eta t).card - delta * ((bohr F eta).card : Real)| ≤
      e * (bohr F eta).card) (hsmall : e < 1 / (Q : Real)^r) : 0 < delta := by
  have h := pattern_density_lower_of_degree F psi J heta hd he t hK hQ hdeg
  linarith

end LeanProofs.GowersSzemeredi
