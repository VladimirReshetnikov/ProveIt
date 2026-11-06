import DiophantineConsistency.Norm38MacroRankValuesSums
import DiophantineConsistency.Norm38MacroPrefixGsmall
import DiophantineConsistency.Norm38MacroPrefixTheta

/-! Candidate remaining symbolic d10 values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankValues
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup03 Norm38MacroPrefixGroup06 ExecutableJones

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
end DiophantineConsistency.Norm38MacroRankValues
