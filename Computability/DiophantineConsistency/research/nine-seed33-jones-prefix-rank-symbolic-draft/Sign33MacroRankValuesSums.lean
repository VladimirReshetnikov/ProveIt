import DiophantineConsistency.Sign33MacroRankComposition
import DiophantineConsistency.Sign33MacroPrefixE
import DiophantineConsistency.Sign33MacroPrefixEll
import DiophantineConsistency.Sign33MacroPrefixLambda

/-! Candidate symbolic d10 sum values; finite sums remain unexpanded. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroRankValues
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroPrefixGroup02 Sign33MacroPrefixGroup06 ExecutableJones

theorem d10_e_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc) =
      ∑ k ∈ codingStar 33 4,
        ((indexZ seed 0 : R) + (pCoefficient seed k : R)) *
          (base a ^ (5 : Nat)) ^ ((5 ^ 34 : Nat) - codingExpo 33 4 k) :=
  (d10_e_carry a).trans (prefix_e a)

theorem d10_ell_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc) =
      ∑ j ∈ Finset.range 33, (base a ^ (5 : Nat)) ^ (5 ^ (j + 1)) :=
  (d10_ell_carry a).trans (prefix_ell a)

theorem d10_lambda_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 6).castSucc.castSucc.castSucc) =
      ∑ j ∈ Finset.range (4 * (5 ^ 34 : Nat)), (base a ^ (5 : Nat)) ^ j :=
  (d10_lambda_carry a).trans (prefix_lambda a)

#print axioms d10_e_value
#print axioms d10_ell_value
#print axioms d10_lambda_value
end DiophantineConsistency.Sign33MacroRankValues
