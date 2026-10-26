import DiophantineConsistency.ThirteenCarrierSoundness

namespace DiophantineConsistency.ThirteenCarrierSoundnessChecks

open ThirteenCarrierSoundness

-- The old i slot receives exactly b*i; the signed ordinate is a supplied map input.
example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (z y : ℤ) :
    parent p v z y 5 = (p 0 * v 0) * v 4 := rfl

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    restored p v 12 = |(ThirteenCarrier.core p v).y| := rfl

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    restored p v 3 = G p v / (p 0 * v 0) + 1 := rfl

-- The first and main norms are the actual thirteen-coordinate factors.
example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    (data p v).P = (ThirteenCarrier.core p v).P ∧
      (data p v).Q = (ThirteenCarrier.core p v).Q := ⟨rfl, rfl⟩

-- The auxiliary estimates cover negative V and negative signed y.
example : (-15 : ℤ) ≠ 0 ∧ |(-15 : ℤ)| < 2 * |(-13 : ℤ)| := by
  exact auxiliary_estimates (S := 2) (by norm_num) (by norm_num)

-- Locally, the m-positivity hypothesis is essential to the transport inequality.
-- With b=V=y=1, m=-2 and G=-1, the identity and magnitude bound both hold.
example : (1 : ℤ) = 1 + 4 * (1 * (-2 - 1 ^ 2 * (-1)) - (-1)) ∧
    |(1 : ℤ)| < 2 * |(1 : ℤ)| ∧ ¬ (0 : ℤ) ≤ -1 := by norm_num

#print axioms core_parent
#print axioms norms_of_zero
#print axioms base_dvd_transport
#print axioms transport_nonneg
#print axioms restores_positive_zero69
#print axioms restores_positive_zero70
#print axioms restores_positive_zero71
#print axioms polynomial_zero_restores

end DiophantineConsistency.ThirteenCarrierSoundnessChecks
