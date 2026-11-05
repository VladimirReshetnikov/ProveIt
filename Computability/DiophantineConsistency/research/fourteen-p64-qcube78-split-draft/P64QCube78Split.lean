import P64QCube79Gap

/-! Draft: first norm and five-square splitting for the sum-minus-two graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube78Split
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ModelArithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_ne_zero (P t k : DiffRing V) (hP : 1≤P) (hk : k≠0) :
    t*t - (P*k)*(P*k+k) ≠ 0 := by
  intro h
  have hn := near_square_ne_zero (2*P+1) (2*t) k (by linarith) hk
  apply hn
  linear_combination 4*h

theorem norm_ne_neg (P t k : DiffRing V) (hP : 2≤P) :
    t*t - (P*k)*(P*k+k) ≠ -1 := by
  intro h
  have hn := consecutive_ne_neg_one P t k hP
  apply hn
  linear_combination h

theorem first_sq_one {a m w n l : DiffRing V}
    (hs : a*a + m*m + w*w + n*n + l*l = 2)
    (ha : a≠0) : a*a=1 := by
  have habs : 1≤|a| := DiscreteOrderedRingFacts.abs_ge_one model_discrete ha
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hn := mul_self_nonneg n
  have hl := mul_self_nonneg l
  have ha2 : a*a≤2 := by linarith
  have hlt : |a| < 2 := by
    by_contra h
    have hge : (2:DiffRing V)≤|a| := le_of_not_gt h
    have hsq := mul_self_le_mul_self (by norm_num : (0:DiffRing V)≤2) hge
    have habssq : |a| * |a|=a*a := abs_mul_abs_self a
    nlinarith
  have hle : |a|≤1 := by
    apply DiscreteOrderedRingFacts.le_of_lt_add_one model_discrete
    have hh : (1:DiffRing V)+1=2 := by norm_num
    rw [hh]
    exact hlt
  have habssq : |a| * |a|=a*a := abs_mul_abs_self a
  nlinarith [abs_nonneg a]

theorem first_one {a : DiffRing V} (hs : a*a=1) (haneg : a≠ -1) : a=1 := by
  rcases DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one model_discrete hs with h | h
  · exact h
  · exact (haneg h).elim

#print axioms P64QCube78Split.norm_ne_zero
#print axioms P64QCube78Split.norm_ne_neg
#print axioms P64QCube78Split.first_sq_one
#print axioms P64QCube78Split.first_one
end P64QCube78Split
