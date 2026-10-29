import DiophantineConsistency.ArithmeticBinaryCarry

/-! The four-block rank identity and population saturation, in every model of IΣ1.
If `R = A + M + q(F+H) + q²(q-1-A) + q³(q-1-F)` with `q = 2^u`, `A,F < q`,
`σ M + σ H ≤ u+2` and `σ R ≥ 3u+2`, then `A` and `M`, and `F` and `H`, have no
common binary one. The lower bound `σ R ≥ 3u+2` is a hypothesis here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSaturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem eq_of_sum_le {a b c d : V} (hab : a ≤ b) (hcd : c ≤ d) (h : b + d ≤ a + c) :
    a = b := by
  exact le_antisymm hab (le_of_add_le_add_right (le_trans ((add_le_add_iff_left b).mpr hcd) h))

theorem population_mul_exp (Z u : V) : population (Z * Exp.exp u) = population Z := by
  simpa using concatenate Z u 0 (exp_pos u)

/-- **Saturation.** -/
theorem saturation (u A F M H R : V) (hA : A < Exp.exp u) (hF : F < Exp.exp u)
    (hR : R = A + M + Exp.exp u * (F + H) + Exp.exp u ^ 2 * (Exp.exp u - 1 - A) +
      Exp.exp u ^ 3 * (Exp.exp u - 1 - F))
    (hMH : population M + population H ≤ u + 2)
    (hlow : 3*u + 2 ≤ population R) :
    NoCarry A M ∧ NoCarry F H := by
  obtain ⟨Y2, hY2def⟩ : ∃ Y2, Y2 = Exp.exp u - 1 - A := ⟨_, rfl⟩
  obtain ⟨Y3, hY3def⟩ : ∃ Y3, Y3 = Exp.exp u - 1 - F := ⟨_, rfl⟩
  rw [← hY2def, ← hY3def] at hR
  have hY2 : Y2 < Exp.exp u := by
    rw [hY2def]
    exact lt_of_le_of_lt tsub_le_self (tsub_lt_self (exp_pos u) one_pos)
  have hR' : R = ((A + M) + (F + H) * Exp.exp u) + (Y3 * Exp.exp u + Y2) * Exp.exp (u+u) := by
    rw [hR, exp_add]; ring
  have hcA : population A + population Y2 = u := by rw [hY2def]; exact complement u A hA
  have hcF : population F + population Y3 = u := by rw [hY3def]; exact complement u F hF
  have hX0 := population_subadditive A M
  have hX1 := population_subadditive F H
  have hs1 : population R ≤ population ((A + M) + (F + H) * Exp.exp u) +
      population ((Y3 * Exp.exp u + Y2) * Exp.exp (u+u)) := by
    rw [hR']; exact population_subadditive _ _
  have hs2 : population ((A + M) + (F + H) * Exp.exp u) ≤
      population (A + M) + population (F + H) := by
    simpa only [population_mul_exp] using population_subadditive (A + M) ((F + H) * Exp.exp u)
  rw [population_mul_exp, concatenate Y3 u Y2 hY2] at hs1
  have hsum : (population A + population M) + (population F + population H) +
      (population Y3 + population Y2) ≤
      (population (A + M) + population (F + H)) + (population Y3 + population Y2) := by
    calc (population A + population M) + (population F + population H) +
          (population Y3 + population Y2)
        = (population A + population Y2) + (population F + population Y3) +
            (population M + population H) := by ring
      _ = u + u + (population M + population H) := by rw [hcA, hcF]
      _ ≤ u + u + (u + 2) := (add_le_add_iff_left _).mpr hMH
      _ = 3*u + 2 := by ring
      _ ≤ population R := hlow
      _ ≤ _ := le_trans hs1 ((add_le_add_iff_right _).mpr hs2)
  have hcore := (add_le_add_iff_right _).mp hsum
  have e0 := eq_of_sum_le hX0 hX1 hcore
  have e1 := eq_of_sum_le hX1 hX0 (by simpa only [add_comm] using hcore)
  exact ⟨(population_add_eq_iff A M).mp e0, (population_add_eq_iff F H).mp e1⟩

/-- **The four-block rank identity**, with every truncated subtraction justified. -/
theorem four_block (q beta J F alpha MC HP : V) (hq : q = beta*J + 1)
    (hgap : 0 < q - F - alpha) (hHP : 1 ≤ HP*J) :
    ((q-1)*(q-F)+alpha)*(q^2-1) + (MC + q*(HP+beta))*J =
      (q-F-alpha-1) + (MC*J+1) + q*(F + (HP*J-1)) + q^2*(q-1-(q-F-alpha-1)) +
        q^3*(q-1-F) := by
  have hle : F + alpha < q := by
    rw [tsub_tsub] at hgap
    exact tsub_pos_iff_lt.mp hgap
  obtain ⟨c, hc⟩ : ∃ c, q - F - alpha = c + 1 :=
    ⟨q - F - alpha - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp hgap)).symm⟩
  obtain ⟨h, hh⟩ : ∃ h, HP*J = h + 1 := ⟨HP*J - 1, (tsub_add_cancel_of_le hHP).symm⟩
  have hq' : q = F + alpha + c + 1 := by
    have : F + alpha + (q - (F + alpha)) = q := add_tsub_cancel_of_le (le_of_lt hle)
    rw [← tsub_tsub, hc] at this
    rw [← this]; ring
  have hbJ : beta*J = F + alpha + c := by
    have : beta*J + 1 = F + alpha + c + 1 := by rw [← hq, hq']
    exact add_right_cancel this
  have e1 : q - 1 = F + alpha + c := by rw [hq', add_tsub_cancel_right]
  have e2 : q - F = alpha + c + 1 := by
    rw [hq', show F + alpha + c + 1 = F + (alpha + c + 1) by ring, add_tsub_cancel_left]
  have e3 : q^2 - 1 = (F + alpha + c) * (F + alpha + c + 2) := by
    rw [hq', show (F + alpha + c + 1)^2 = (F + alpha + c) * (F + alpha + c + 2) + 1 by ring,
      add_tsub_cancel_right]
  have e5 : F + alpha + c - c = F + alpha := add_tsub_cancel_right _ _
  have e7 : F + alpha + c - F = alpha + c := by
    rw [show F + alpha + c = F + (alpha + c) by ring, add_tsub_cancel_left]
  have e8 : (MC + q*(HP+beta))*J = MC*J + q*(HP*J) + q*(beta*J) := by ring
  rw [e8, hh, hbJ, hc, add_tsub_cancel_right, add_tsub_cancel_right, e1, e2, e3, e5, e7]
  rw [hq']
  ring

end DiophantineConsistency.ArithmeticSaturation
