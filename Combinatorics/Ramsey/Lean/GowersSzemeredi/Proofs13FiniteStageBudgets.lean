import GowersSzemeredi.Proofs13TenRowBudgets

/-! All row-extraction integer budgets above the singleton scale, with no
asymptotic threshold or extra coefficient assumptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_finite_integer_budgets {alpha : Real} (ha : 0 < alpha) (haone : alpha ≤ 1)
    (N q p L Q : Nat) (hN : 1 ≤ N) (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)))
    (hfloor : IsNatFloor
      (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * q))) p)
    (hL : L = p ∨ L + 1 = p)
    (hQ : (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q)
    (hlarge : 1 ≤ section13Zeta alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha))) :
    ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
      section13Zeta alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
      (L : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
        section10Zeta (alpha ^ 32 / 16) / m  := by
  have htarget := section13_row_target_antitone ha N hN (by norm_num : (10 : Real) ≤ 13)
  obtain ⟨m, hm, hsize, hupper, hlower, hbohr⟩ := section13_ten_integer_budgets
    ha haone N q p L Q hN hq hqBound hfloor hL hQ (hlarge.trans htarget)
  exact ⟨m, hm, hsize, hupper, htarget.trans hlower, hbohr⟩

end LeanProofs.GowersSzemeredi
