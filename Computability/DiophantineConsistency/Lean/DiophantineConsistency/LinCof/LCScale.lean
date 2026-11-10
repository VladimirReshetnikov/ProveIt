import DiophantineConsistency.LinCof.LCOrientation
import DiophantineConsistency.BFS943.Trace80Parity

/-! # The scale divisibility: `Y = (2t + 1) q³`

In the linear-cofactor family the scale `Y` is a free unknown, and the carrier only gives
`M ∣ H (Y − q³)` with `M = 2q³` (`LCCarrier.M_dvd_H_mul`). The cofactor `H = 4a + 3` is odd,
but it can only be cancelled against `M` once `M` is known to be a power of two, that is after
the orientation step: `X = 2^R` and `q > 0` make `q` a power of two
(`LCOrientation.q_pow2`), so `M = 2q³` is a power of two, and
`Trace80Parity.pow2_cancel_odd` gives `M ∣ Y − q³`.

The result, `Y = (2t + 1) q³` (`Y_odd_mul`), is exactly the shape of the scale that package 138
has by construction; `q_cube_dvd_Y` is the divisibility used by the leaf fact `ydiv`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCScale
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCCarrier LCOrientation
open ZRowsCoprimeSquares (abs_eq_ι)
open P138Bootstrap (int_split)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An odd element of the difference ring has an odd absolute value. -/
theorem abs_odd {H m : DiffRing V} (hH : H = 2 * m + 1) :
    ∃ hn : V, |H| = ι hn ∧ ¬ (2 : V) ∣ hn := by
  obtain ⟨hn, hhn⟩ := abs_eq_ι H
  refine ⟨hn, hhn, ?_⟩
  rintro ⟨c, hc⟩
  have h2 : |H| = 2 * ι c := by rw [hhn, hc, map_mul, map_ofNat]
  rcases abs_choice H with h' | h' <;> rw [h'] at h2
  · have h1 : (2 : DiffRing V) * (ι c - m) = 1 := by linear_combination hH - h2
    rcases int_split (ι c - m - 1) with h0 | h0 <;> linarith
  · have h1 : (2 : DiffRing V) * (-ι c - m) = 1 := by linear_combination hH + h2
    rcases int_split (-ι c - m - 1) with h0 | h0 <;> linarith

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **The scale.** At a zero with `X = 2^R`, `Y = (2t + 1) q³`. -/
theorem Y_odd_mul (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hwt : Weight wt)
    (hz : valueK p x κ ω Λ ψ wt = 0) (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) :
    ∃ t : DiffRing V, (𝓡).Y = (2 * t + 1) * (𝓡).q ^ 3 := by
  obtain ⟨Qn, hq, hpow⟩ := q_pow2 p x κ ω Λ ψ wt hp Rn hX
  obtain ⟨m, hm⟩ := H_odd p x κ ω Λ ψ wt
  obtain ⟨hn, hhn, hodd⟩ := abs_odd hm
  have hP : Pow2 (2 * (Qn * Qn * Qn)) := pow2_mul_two.mpr ((hpow.mul hpow).mul hpow)
  have hM : (ι (2 * (Qn * Qn * Qn)) : DiffRing V) = 2 * (𝓡).q ^ 3 := by
    rw [hq]; simp only [map_mul, map_ofNat]; ring
  have hd : (ι (2 * (Qn * Qn * Qn)) : DiffRing V) ∣ (𝓡).H * ((𝓡).Y - (𝓡).q ^ 3) := by
    rw [hM, ← M_eq]; exact M_dvd_H_mul ψ wt hp h hwt hz
  have hd' : (ι (2 * (Qn * Qn * Qn)) : DiffRing V) ∣ ι hn * ((𝓡).Y - (𝓡).q ^ 3) := by
    rw [← hhn]
    rcases abs_choice (𝓡).H with h' | h' <;> rw [h']
    · exact hd
    · rw [neg_mul]; exact (dvd_neg).mpr hd
  obtain ⟨t, ht⟩ := Trace80Parity.pow2_cancel_odd _ hn _ hP hodd hd'
  exact ⟨t, by linear_combination ht + t * hM⟩

/-- **`q³ ∣ Y`** at a zero with `X = 2^R`. -/
theorem q_cube_dvd_Y (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hwt : Weight wt)
    (hz : valueK p x κ ω Λ ψ wt = 0) (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) :
    (𝓡).q ^ 3 ∣ (𝓡).Y := by
  obtain ⟨t, ht⟩ := Y_odd_mul ψ wt hp h hwt hz Rn hX
  exact ⟨2 * t + 1, by rw [ht]; ring⟩

end Regs

#print axioms abs_odd
#print axioms Y_odd_mul
#print axioms q_cube_dvd_Y

end DiophantineConsistency.LCScale
