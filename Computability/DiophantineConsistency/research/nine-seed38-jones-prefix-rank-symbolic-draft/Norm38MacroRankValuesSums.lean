import DiophantineConsistency.Norm38MacroRankComposition
import DiophantineConsistency.Norm38MacroPrefixE
import DiophantineConsistency.Norm38MacroPrefixEll
import DiophantineConsistency.Norm38MacroPrefixLambda

/-! Candidate symbolic d10 sum values; finite sums remain unexpanded. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankValues
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup02 Norm38MacroPrefixGroup06 ExecutableJones

theorem d10_e_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc) =
      ∑ k ∈ codingStar 38 4,
        ((indexZ seed 0 : R) + (pCoefficient seed k : R)) *
          (base a ^ (5 : Nat)) ^ ((5 ^ 39 : Nat) - codingExpo 38 4 k) :=
  (d10_e_carry a).trans (prefix_e a)

theorem d10_ell_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc) =
      ∑ j ∈ Finset.range 38, (base a ^ (5 : Nat)) ^ (5 ^ (j + 1)) :=
  (d10_ell_carry a).trans (prefix_ell a)

theorem d10_lambda_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 6).castSucc.castSucc.castSucc) =
      ∑ j ∈ Finset.range (4 * (5 ^ 39 : Nat)), (base a ^ (5 : Nat)) ^ j :=
  (d10_lambda_carry a).trans (prefix_lambda a)

#print axioms d10_e_value
#print axioms d10_ell_value
#print axioms d10_lambda_value
end DiophantineConsistency.Norm38MacroRankValues
