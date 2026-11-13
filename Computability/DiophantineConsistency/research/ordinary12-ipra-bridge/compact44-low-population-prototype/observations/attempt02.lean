import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactLowPopulation
open Finset CompactListMask CompactConcreteMask
open DiophantineConsistency
open ArithmeticMaskData
open scoped BigOperators

private theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  have hr : (List.range n).toFinset = range n := by ext; simp
  simpa only [hr] using (List.sum_toFinset f (List.nodup_range (n := n))).symm

private theorem pop_ones : pcF 67 (2^67-1)=67 := by decide +kernel
private theorem pop_ordinary : pcF 67 (2^67-2)=66 := by decide +kernel
private theorem pop_special : pcF 67 (2^67-4)=65 := by decide +kernel

theorem list_population_general (len special : ℕ) (S : Finset ℕ)
    (hS : S ⊆ range len) (hspecial : special ∈ S) :
    ((digits (2^67) len special S).map (pcF 67)).sum+S.card+1=len*67 := by
  have hspecial_range : special∈range len := hS hspecial
  simp only [digits, List.map_map]
  rw [sum_map_range]
  have hpoint (j : ℕ) : pcF 67 (digit (2^67) special S j) +
      (if j∈S then 1 else 0) + (if j=special then 1 else 0) = 67 := by
    by_cases hs : j=special
    · subst j
      simp only [digit, if_pos rfl, if_pos hspecial]
      rw [pop_special]
    · by_cases hj : j∈S
      · simp only [digit,if_neg hs,if_pos hj]
        rw [pop_ordinary]
      · simp only [digit,if_neg hs,if_neg hj]
        rw [pop_ones]
  have he : (∑ j ∈ range len, (pcF 67 (digit (2^67) special S j) +
      (if j∈S then 1 else 0) + (if j=special then 1 else 0))) = len*67 := by
    simp_rw [hpoint]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at he
  have hs : (∑ j ∈ range len, if j∈S then 1 else 0) = S.card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hS]
    simp
  have hexc : (∑ j ∈ range len, if j=special then 1 else 0) = 1 := by simp [hspecial_range]
  rw [hs,hexc] at he
  exact he

theorem list_population (hcard : support.card=985) :
    ((digits (2^67) 8807 1063 support).map (pcF 67)).sum=589083 := by
  have h := list_population_general 8807 1063 support support_bounded special_mem
  rw [hcard] at h
  omega

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_population (hcard : support.card=985) :
    population ((Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ):V)=589083 := by
  have h := population_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 support)
    (digits_lt _ _ _ _ (by norm_num))
  rw [list_population hcard] at h
  simpa using h
end Model
end CompactLowPopulation
#print axioms CompactLowPopulation.list_population
#print axioms CompactLowPopulation.model_population
