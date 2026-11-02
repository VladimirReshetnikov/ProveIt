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

theorem list_population (hcard : support.card=985) :
    ((digits (2^67) 8807 1063 support).map (pcF 67)).sum=589083 := by
  simp only [digits, List.map_map]
  rw [sum_map_range]
  have hpoint (j : ℕ) : pcF 67 (digit (2^67) 1063 support j) +
      (if j∈support then 1 else 0) + (if j=1063 then 1 else 0) = 67 := by
    by_cases hs : j=1063
    · subst j
      simp [digit, special_mem, pop_special]
    · by_cases hj : j∈support
      · simp [digit,hs,hj,pop_ordinary]
      · simp [digit,hs,hj,pop_ones]
  have he : (∑ j ∈ range 8807, (pcF 67 (digit (2^67) 1063 support j) +
      (if j∈support then 1 else 0) + (if j=1063 then 1 else 0))) = 8807*67 := by
    simp_rw [hpoint]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at he
  have hsupport : (∑ j ∈ range 8807, if j∈support then 1 else 0) = 985 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset support_bounded]
    simpa using hcard
  have hspecial : (∑ j ∈ range 8807, if j=1063 then 1 else 0) = 1 := by simp
  rw [hsupport,hspecial] at he
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
