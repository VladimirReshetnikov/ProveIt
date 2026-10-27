import DiophantineConsistency.NativeAdaptiveCarrierBootstrap

namespace DiophantineConsistency.NativeAdaptiveCarrierBootstrapChecks

open NativeAdaptiveCarrierBootstrap
set_option Elab.async false

-- The first carrier really admits a negative integral root on its positive
-- parameter domain: q=2, ell=1, k=7, r=4, Y=8, Bt=2 give Z/M=-3.
example : firstZ 2 1 7 4 8 2 = -24 := by norm_num [firstZ]
example : firstA0 2 1 7 4 8 2 = 0 := by norm_num [firstA0, firstZ]
example : ∃ s b tau : ℤ, 0 < s ∧ 0 < b ∧
    (8 : ℤ) = 2 ^ 3 * s ∧ (2 : ℤ) = (2 - 1) * b ∧
    firstZ 2 1 7 4 8 2 = (2 ^ 3 * (2 - 1)) * tau ∧
    tau ^ 2 = (1 : ℤ) * (1 + 7) + 1 ∧
    tau = 1 + 7 + 4 + s - ((2 - 1) * 7 + 1) * b ∧
    0 < |tau| ∧ |tau| < 1 + 7 := by
  exact first_carrier_integral_positive (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [firstA0, firstZ])

-- q divisible by three is allowed; no coprimality premise is hidden.
example : firstA0 3 1 7 9 27 2 = 0 := by norm_num [firstA0, firstZ]
example : firstZ 3 1 7 9 27 2 = 54 * 3 := by norm_num [firstZ]

-- Classification retains both root signs, and the smallest first index.
example : ∃ n : ℕ, 0 < n ∧
    |(-3 : ℤ)| = (Pell.xn (by decide : 1 < 3) n : ℤ) ∧
    (2 : ℤ) = 2 * (Pell.yn (by decide : 1 < 3) n : ℤ) := by
  exact classify_signed_first_norm (by norm_num : (0 : ℤ) < 1)
    (by norm_num : (0 : ℤ) < 2) (by norm_num : (-3 : ℤ) ^ 2 = 1 + 1 * (1 + 1) * 2 ^ 2)

example {q K X F alpha Bt : ℤ} (hq : 0 < q) (hK : 0 ≤ K)
    (hX : 0 < X) (hF : 0 < F)
    (hb : Bt = (q * K + X) * (q - F - alpha) - q * F) (hp : 0 < Bt) :
    0 < q - F - alpha := transport_positive hq hK hX hF hb hp

#print axioms firstZ
#print axioms firstA0
#print axioms first_carrier_integral_positive
#print axioms transport_positive
#print axioms classify_signed_first_norm

end DiophantineConsistency.NativeAdaptiveCarrierBootstrapChecks
