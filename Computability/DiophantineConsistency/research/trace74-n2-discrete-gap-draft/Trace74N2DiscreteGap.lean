import Trace74FirstIndexGeometry

/-! UNCHECKED DRAFT. A discrete multiple-of-q window obstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2DiscreteGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_divisible_window (q X Y : V) (hq4 : 4≤q)
    (hX : q∣X) (hY : q∣Y) (hleft : X<2*Y) (hright : 2*Y<X+3) : False := by
  obtain ⟨a,ha⟩ := hY
  obtain ⟨b,hb⟩ := hX
  have hba : b<2*a := by
    by_contra hn
    have hle : 2*a≤b := le_of_not_gt hn
    have hmul : q*(2*a)≤q*b := mul_le_mul_of_nonneg_left hle (by simp)
    have hc : 2*Y≤X := by
      calc
        2*Y= q*(2*a) := by rw [ha]; ring
        _≤q*b := hmul
        _=X := hb.symm
    exact (not_le_of_gt hleft) hc
  have hstep : X+q≤2*Y := calc
    X+q=q*(b+1) := by rw [hb]; ring
    _≤q*(2*a) := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hba) (by simp)
    _=2*Y := by rw [ha]; ring
  have h3q : X+3<X+q := by
    simpa only [add_comm] using add_lt_add_left (lt_of_lt_of_le (by norm_num : (3:V)<4) hq4) X
  exact (not_lt_of_ge hstep) (lt_trans hright h3q)

theorem graph_XY_window_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hq4 : 4≤q p v) (hleft : X p v<2*Y p v) (hright : 2*Y p v<X p v+3) : False := by
  have hX : q p v∣X p v := by
    refine ⟨v 5,?_⟩
    change v 5*q p v=q p v*v 5
    ring
  have hY : q p v∣Y p v := by
    refine ⟨q p v*q p v*v 6,?_⟩
    change q p v*q p v*q p v*v 6=q p v*(q p v*q p v*v 6)
    ring
  exact no_divisible_window (q p v) (X p v) (Y p v) hq4 hX hY hleft hright

#print axioms Trace74N2DiscreteGap.no_divisible_window
#print axioms Trace74N2DiscreteGap.graph_XY_window_impossible
end Trace74N2DiscreteGap
