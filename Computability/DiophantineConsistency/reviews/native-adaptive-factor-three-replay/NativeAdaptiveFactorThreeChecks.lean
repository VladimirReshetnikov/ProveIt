import DiophantineConsistency.NativeAdaptiveFactorThree

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveFactorThreeChecks
open NativeAdaptiveFactorThree

-- All signs and zero are allowed; no canonical source or rank is assumed.
example (q Y X t : ℤ) (hY : q^3 ∣ Y)
    (hd : q^5 ∣ (4*Y*(X+1)+3)*t) : q^4 ∣ t := cancel_factor_three hY hd

example (q Y X v : ℤ) (hY : q^3 ∣ Y)
    (hd : q^5 ∣ (4*Y*(X+1)+3)*(q*X*Y-v)) : q^4 ∣ v := index_difference_dvd hY hd

-- Losing one power is necessary for unrestricted J: q=3,Y=27,X=1,t=81.
example : (3 : ℤ)^3 ∣ 27 ∧
    (3 : ℤ)^5 ∣ (4*27*(1+1)+3)*81 ∧ ¬ (3 : ℤ)^5 ∣ 81 := by norm_num

example (q : ℤ) (h : ¬ (3 : ℤ) ∣ q) : ∃ a b : ℤ, a*q+b*3=1 := bezout_three h

example (X t : ℤ) (hd : (0 : ℤ)^5 ∣ (4*0*(X+1)+3)*t) : (0 : ℤ)^4 ∣ t :=
  cancel_factor_three (by simp) hd

#print axioms cancel_four_of_unit_residue
#print axioms bezout_three
#print axioms cancel_factor_three
#print axioms index_difference_dvd
end DiophantineConsistency.NativeAdaptiveFactorThreeChecks
