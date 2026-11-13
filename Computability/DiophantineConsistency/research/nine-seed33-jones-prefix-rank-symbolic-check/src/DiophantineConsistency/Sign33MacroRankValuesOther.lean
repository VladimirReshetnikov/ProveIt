import DiophantineConsistency.Sign33MacroRankValuesSums
import DiophantineConsistency.Sign33MacroPrefixGsmall
import DiophantineConsistency.Sign33MacroPrefixTheta

/-! Candidate remaining symbolic d10 values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroRankValues
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroPrefixGroup03 Sign33MacroPrefixGroup06 ExecutableJones

theorem d10_b_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a :=
  (d10_b_carry a).trans (d9_b a)

theorem d10_g_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 7).castSucc.castSucc) = a ⟨1, by decide⟩ + ((1 : Int) : R) :=
  (d10_g_carry a).trans (prefix_g a)

theorem d10_theta_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 8).castSucc) = base a ^ (5 : Nat) -
      ((2 : Int) : R) * (indexZ seed 0 : R) :=
  (d10_theta_carry a).trans (prefix_theta a)

#print axioms d10_b_value
#print axioms d10_g_value
#print axioms d10_theta_value
end DiophantineConsistency.Sign33MacroRankValues
