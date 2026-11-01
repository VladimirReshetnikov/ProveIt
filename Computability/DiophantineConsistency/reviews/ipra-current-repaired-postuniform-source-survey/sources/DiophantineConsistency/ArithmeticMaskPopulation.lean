import DiophantineConsistency.ArithmeticRepunit

/-! The repeated mask population (spec A5), in every model of IΣ1.
For blocks `MC, HP < 2^d` with `MC` even, `HP ≡ 4 (mod 8)`, `d ≥ 3` and
`σ MC + σ HP = d`, the incremented low mask and the decremented high mask
repeated `N ≥ 1` times by the represented repunit have total population
`d·N + 2`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticMaskPopulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The repunit is `1 (mod 8)` at width at least three. -/
theorem rep_eight (d N : V) (hd : 3 ≤ d) (hN : 0 < N) : ∃ j, rep d N = 8*j + 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 :=
    ⟨N - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp hN)).symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = 3 + e := ⟨d - 3, (add_tsub_cancel_of_le hd).symm⟩
  refine ⟨rep (3+e) M * Exp.exp e, ?_⟩
  rw [rep_succ, exp_add]
  have h8 : Exp.exp (3:V) = 8 := by
    rw [show (3:V) = 2 + 1 by norm_num, exp_succ, show (2:V) = 1 + 1 by norm_num, exp_succ,
      exp_one]
    norm_num
  rw [h8]
  ring

theorem population_eight_four (Y : V) :
    population (8*Y+4) = population Y + 1 ∧ population (8*Y+3) = population Y + 2 := by
  constructor
  · rw [show 8*Y+4 = 2*(2*(2*Y+1)) by ring, population_even, population_even, population_odd]
  · rw [show 8*Y+3 = 2*(2*(2*Y)+1)+1 by ring, population_odd, population_odd, population_even]
    ring

/-- **Repeated mask population.** -/
theorem repeated_mask_population (d N MC HP : V) (hd : 3 ≤ d) (hN : 0 < N)
    (hMC : MC < Exp.exp d) (hHP : HP < Exp.exp d)
    (hMC2 : MC % 2 = 0) (hHP8 : HP % 8 = 4)
    (hsum : population MC + population HP = d) :
    population (MC * rep d N + 1) + population (HP * rep d N - 1) = d*N + 2 := by
  have hlow : population (MC * rep d N + 1) = N * population MC + 1 := by
    have he : MC = 2*(MC/2) := by
      have := div_add_mod MC 2
      rw [hMC2, add_zero] at this
      exact this.symm
    have : MC * rep d N + 1 = 2*(MC/2 * rep d N) + 1 := by
      conv_lhs => rw [he]
      ring
    rw [this, population_odd, ← population_even (MC/2 * rep d N), ← mul_assoc, ← he,
      population_repeat d MC N hMC]
  obtain ⟨j, hj⟩ := rep_eight d N hd hN
  have hHPd : HP = 8*(HP/8) + 4 := by
    have := div_add_mod HP 8
    rw [hHP8] at this
    exact this.symm
  set Y := 8*(HP/8)*j + HP/8 + 4*j
  have hprod : HP * rep d N = 8*Y + 4 := by
    rw [hj]
    conv_lhs => rw [hHPd]
    simp only [Y]
    ring
  have hhigh : population (HP * rep d N - 1) = N * population HP + 1 := by
    have hrep := population_repeat d HP N hHP
    rw [hprod] at hrep ⊢
    rw [show 8*Y+4-1 = 8*Y+3 by
      rw [show 8*Y+4 = (8*Y+3)+1 by ring, add_tsub_cancel_right]]
    rw [(population_eight_four Y).2]
    rw [(population_eight_four Y).1] at hrep
    rw [show population Y + 2 = (population Y + 1) + 1 by ring, hrep]
  rw [hlow, hhigh, ← hsum]
  ring

end DiophantineConsistency.ArithmeticMaskPopulation
