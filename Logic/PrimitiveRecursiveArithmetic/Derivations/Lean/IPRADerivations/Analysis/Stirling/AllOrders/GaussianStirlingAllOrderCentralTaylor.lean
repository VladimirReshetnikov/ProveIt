import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelDerivative

/-!
# Exact central Taylor expansion of the cleared Bernoulli polynomial

Only even binomial powers survive in the central difference. The
quadratic term is the genuine second derivative, and every remaining
term has at least four powers of the mesh increment.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralTaylor

open Finset

def quadratic (j : ℕ) : ℕ := j*(j-1)

theorem choose_two (j : ℕ) : 2*j.choose 2 = quadratic j := by
  rw [Nat.choose_two_right, quadratic]
  have h : Even (j*(j-1)) := by
    rcases Nat.even_or_odd j with h | h
    · exact h.mul_right _
    · by_cases hz : j=0
      · simp [hz]
      · have he : Even (j-1) := by
          obtain ⟨d,hd⟩ := h
          exact ⟨d,by omega⟩
        exact he.mul_left _
  obtain ⟨k,hk⟩ := h
  omega

def evenTailTerm {R : Type*} [CommRing R] (j k : ℕ) (x h : R) : R :=
  if 4≤k ∧ Even k then (2*j.choose k : ℕ)*x^(j-k)*h^k else 0

theorem central_monomial {R : Type*} [CommRing R] (j : ℕ) (x h : R) :
    (x+h)^j+(x-h)^j-2*x^j-(quadratic j : ℕ)*x^(j-2)*(h*h) =
      ∑ k ∈ range (j+1), evenTailTerm j k x h := by
  have combine : (x+h)^j+(x-h)^j =
      ∑ k ∈ range (j+1), if Even k then (2*j.choose k : ℕ)*x^(j-k)*h^k else (0:R) := by
    rw [_root_.add_comm x h,sub_eq_add_neg,_root_.add_comm x (-h),add_pow,add_pow,← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos he,he.neg_pow]
      push_cast
      ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho),ho.neg_pow]
      ring
  rw [combine]
  have rewrite (k : ℕ) :
      (if Even k then ((2*j.choose k : ℕ) : R)*x^(j-k)*h^k else 0) =
      (if k=0 then 2*x^j else 0)+(if k=2 then (quadratic j : ℕ)*x^(j-2)*(h*h) else 0)+evenTailTerm j k x h := by
    by_cases h0 : k=0
    · subst k
      simp [evenTailTerm]
    by_cases h2 : k=2
    · subst k
      simp [evenTailTerm,choose_two]
      ring
    rcases Nat.even_or_odd k with he | ho
    · have hk : 4≤k := by
        obtain ⟨i,hi⟩ := he
        omega
      have hc : 4≤k ∧ Even k := ⟨hk,he⟩
      simp [if_neg h0,if_neg h2,evenTailTerm,hc]
    · have hn := Nat.not_even_iff_odd.mpr ho
      simp [if_neg hn,if_neg h0,if_neg h2,evenTailTerm,show ¬ (4≤k ∧ Even k) from fun h => hn h.2]
  simp_rw [rewrite]
  rw [sum_add_distrib,sum_add_distrib]
  have first : ∑ k ∈ range (j+1), (if k=0 then 2*x^j else 0) = 2*x^j := by simp
  have second : ∑ k ∈ range (j+1), (if k=2 then (quadratic j : ℕ)*x^(j-2)*(h*h) else 0) =
      (quadratic j : ℕ)*x^(j-2)*(h*h) := by
    by_cases hj : 2≤j
    · have hmem : 2 ∈ range (j+1) := mem_range.mpr (by omega)
      rw [sum_eq_single_of_mem 2 hmem]
      · simp
      · intro k _ hk
        simp [hk]
    · have hz : quadratic j = 0 := by
        have h : j=0 ∨ j=1 := by omega
        rcases h with h | h <;> subst j <;> decide
      simp [hz]
  rw [first,second]
  ring

def homogeneous {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d+1) → ℤ) (x M : R) : R :=
  ∑ j, (a j : R)*x^(j : ℕ)*M^(d-(j : ℕ))

def curvature {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d+1) → ℤ) (x M : R) : R :=
  ∑ j, (a j : R)*(quadratic j : ℕ)*x^((j : ℕ)-2)*M^(d-(j : ℕ))

def remainder {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d+1) → ℤ) (x h M : R) : R :=
  ∑ j : Fin (d+1), (a j : R)*(∑ k ∈ range ((j : ℕ)+1), evenTailTerm (j : ℕ) k x h)*M^(d-(j : ℕ))

theorem central_polynomial {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d+1) → ℤ) (x h M : R) :
    homogeneous d a (x+h) M+homogeneous d a (x-h) M-2*homogeneous d a x M-h*h*curvature d a x M =
      remainder d a x h M := by
  unfold homogeneous curvature remainder
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  simp only [← mul_sum]
  linear_combination (a j : R)*M^(d-(j : ℕ))*central_monomial (j : ℕ) x h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralTaylor
