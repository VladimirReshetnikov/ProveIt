import DiophantineConsistency.ArithmeticMaskConstants
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHighPopulation
open DiophantineConsistency
open ArithmeticMaskData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticMaskConstants

def mu : ℕ := 2^51-2
def padding : ℕ := 2^65-1
def lastPadding : ℕ := 2^19-1

def highDigits : List ℕ :=
  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++
  List.replicate 42 0 ++ List.replicate 9 1 ++
  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++
  List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]

theorem digits_length : highDigits.length = 8807 := by
  simp [highDigits]

theorem digit_lt (x : ℕ) (hx : x ∈ highDigits) : x < 2^67 := by
  simp only [highDigits, List.mem_append, List.mem_replicate, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;>
    simp_all [mu, padding, lastPadding] <;> norm_num

private theorem pop_zero : pcF 67 0 = 0 := by decide +kernel
private theorem pop_one : pcF 67 1 = 1 := by decide +kernel
private theorem pop_four : pcF 67 4 = 1 := by decide +kernel
private theorem pop_mu : pcF 67 mu = 50 := by decide +kernel
private theorem pop_padding : pcF 67 padding = 65 := by decide +kernel
private theorem pop_last : pcF 67 lastPadding = 19 := by decide +kernel

theorem digits_population : (highDigits.map (pcF 67)).sum = 986 := by
  simp [highDigits, List.map_replicate, List.sum_replicate,
    pop_zero, pop_one, pop_four, pop_mu, pop_padding, pop_last]

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_population :
    population ((Nat.ofDigits (2^67) highDigits : ℕ) : V) = 986 := by
  have h := population_ofDigits (V:=V) 67 highDigits digit_lt
  rw [digits_population] at h
  simpa using h

theorem model_lt : ((Nat.ofDigits (2^67) highDigits : ℕ) : V) < Exp.exp ((67:V)*8807) := by
  have h := ofDigits_lt_exp (V:=V) 67 highDigits digit_lt
  rw [digits_length] at h
  exact h
end Model
end CompactHighPopulation
#print axioms CompactHighPopulation.model_population
#print axioms CompactHighPopulation.model_lt
