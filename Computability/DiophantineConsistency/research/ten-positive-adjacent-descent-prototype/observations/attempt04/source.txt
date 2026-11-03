import TenPositiveDoubling
import ScaledSquare

/-! First denominator-divisibility step of the adjacent rational-Pell descent.
This module does not prove the descent or graph-to-halt equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveAdjacentDenominator
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open DiophantineConsistency.ModelProductPell
open TenPositiveDoubling
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A unit certificate between r and m implies one between r and m². -/
theorem bez_right_square (r m : V) (hu : Bez r m 1) : Bez r (m*m) 1 := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists r (m*m)
  have hgm : Bez g m 1 := restrict_certificate hg.1 hu
  have hgd : g∣m := unit_certificate_cancel (pp_bez_symm hgm) hg.2.1
  have hg1 : g∣(1:V) := bez_divisor hu hg.1 hgd
  obtain ⟨t,ht⟩ := hg1
  have hgpos : 0<g := pos_of_mul_pos_left (by rw [←ht]; simp) (by simp)
  have hgone : g=1 := le_antisymm (le_of_dvd (by simp : (0:V)<1) ⟨t,ht⟩)
    (pos_iff_one_le.mp hgpos)
  simpa [hgone] using hg.2.2

/-- Clearing a reduced denominator in `Q*v² - B*(r/m)² = 1` forces
its square to divide B. The positive denominator is explicit. -/
theorem denominator_square_divides (Q B v r m : V)
    (hm : 0<m) (hu : Bez r m 1)
    (h : Q*((m*v)*(m*v))=m*m+B*(r*r)) : m*m∣B := by
  have hsum : m*m∣m*m+B*(r*r) := ⟨Q*(v*v),by rw [←h]; ring⟩
  have hd : m*m∣B*(r*r) := by
    have hm2 : 0<m*m := mul_pos hm hm
    apply mod_eq_zero_iff_dvd.mp
    obtain ⟨t,ht⟩ := hsum
    have hs := congrArg (fun x : V => x%(m*m)) ht
    simpa [mod_add,mod_mul,hm2] using hs
  have hunit := bez_right_square r m hu
  have hd1 : m*m∣r*(B*r) := by simpa only [mul_comm,mul_left_comm,mul_assoc] using hd
  have hd2 : m*m∣B*r := unit_certificate_cancel hunit hd1
  have hd3 : m*m∣r*B := by simpa only [mul_comm] using hd2
  exact unit_certificate_cancel hunit hd3

#print axioms TenPositiveAdjacentDenominator.bez_right_square
#print axioms TenPositiveAdjacentDenominator.denominator_square_divides
end TenPositiveAdjacentDenominator
