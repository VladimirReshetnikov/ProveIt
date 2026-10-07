import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem retained_pairing_from_mean_comparison {PH PG m h g v τ lam ε δ : ℝ}
    (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : |PH - m * h| ≤ δ * m * lam * (v + τ))
    (hPG : |PG - m * g| ≤ δ * m * (v + τ))
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g)
    (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ m * lam * (1 + 2 * ε) * τ := by
  have hu := (abs_le.mp hPH).2
  have hl := (abs_le.mp hPG).1
  have hp := mul_le_mul_of_nonneg_left hl (mul_nonneg (by linarith : 0 ≤ 1 + ε) hlam)
  have hmh := mul_le_mul_of_nonneg_left hh hm
  have hc : PH - (1 + ε) * lam * PG ≤
      m * lam * (τ - ε * g + δ * (2 + ε) * (v + τ)) := by
    nlinarith
  have hi : τ - ε * g + δ * (2 + ε) * (v + τ) ≤ (1 + 2 * ε) * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hg hε,
      mul_le_mul_of_nonneg_right hsmall (add_nonneg hv hτ)]
  exact hc.trans ((mul_le_mul_of_nonneg_left hi (mul_nonneg hm hlam)).trans_eq (by ring))

end Erdos3

end

section

namespace Erdos3

theorem retained_pairing_upper_with_shell {PH PG m h g v τ lam ε δ EH EG : ℝ}
    (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : PH ≤ m * h + δ * m * lam * (v + τ) + EH)
    (hPG : m * g - δ * m * (v + τ) - EG ≤ PG)
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ m * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  have hp := mul_le_mul_of_nonneg_left hPG (mul_nonneg (by linarith : 0 ≤ 1 + ε) hlam)
  have hmh := mul_le_mul_of_nonneg_left hh hm
  have hc : PH - (1 + ε) * lam * PG ≤
      m * lam * (τ - ε * g + δ * (2 + ε) * (v + τ)) + EH + (1 + ε) * lam * EG := by
    nlinarith
  have hi : τ - ε * g + δ * (2 + ε) * (v + τ) ≤ (1 + 2 * ε) * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hg hε,
      mul_le_mul_of_nonneg_right hsmall (add_nonneg hv hτ)]
  have hmul := mul_le_mul_of_nonneg_left hi (mul_nonneg hm hlam)
  nlinarith

theorem retained_pairing_abs_with_shell {PH PG m h g v τ lam ε δ EH EG : ℝ}
    (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : |PH - m * h| ≤ EH + δ * m * lam * (v + τ))
    (hPG : |PG - m * g| ≤ EG + δ * m * (v + τ))
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ m * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  apply retained_pairing_upper_with_shell hm hlam hv hτ hε _ _ hh hg hsmall
  · linarith [(abs_le.mp hPH).2]
  · linarith [(abs_le.mp hPG).1]

theorem retained_atom_from_normalized_errors {PH PG a m h g v τ lam ε δ EH EG UH UG : ℝ}
    (ha : 0 ≤ a) (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : |PH - (a * m) * h| ≤ EH + a * m * (4 * lam * (v + τ)) * UH)
    (hPG : |PG - (a * m) * g| ≤ EG + a * m * (2 * (v + τ)) * UG)
    (hUH : 4 * UH ≤ δ) (hUG : 2 * UG ≤ δ)
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ (a * m) * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  apply retained_pairing_abs_with_shell (mul_nonneg ha hm) hlam hv hτ hε _ _ hh hg hsmall
  · have hmul := mul_le_mul_of_nonneg_left hUH
      (mul_nonneg (mul_nonneg (mul_nonneg ha hm) hlam) (add_nonneg hv hτ))
    exact hPH.trans (by nlinarith)
  · have hmul := mul_le_mul_of_nonneg_left hUG
      (mul_nonneg (mul_nonneg ha hm) (add_nonneg hv hτ))
    exact hPG.trans (by nlinarith)

end Erdos3

end

end OAI
