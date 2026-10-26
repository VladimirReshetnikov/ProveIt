import BusyBeaver.ZFC.ArithmeticSequenceHistory

set_option autoImplicit false
set_option Elab.async false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticSequenceHistory

-- The represented formulas are closed syntax values with no model parameter.
example (d : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 2 := historyDef d
example (d : 𝚺₁.Semisentence 3) : 𝚫₁.Semisentence 2 := historyDeltaDef d
example (d : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 2 := valueDef d
example (d : 𝚺₁.Semisentence 3) : 𝚫₁.Semisentence 2 := valueDeltaDef d

section
variable (d : 𝚺₁.Semisentence 3)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (step : V → V → V) [𝚺₁-Function₂[V] step via d]

example (code : V) : ∃! s, (historyDef d).val.Evalb ![s, code] := history_total d step code
example (code : V) : ∃! r, (valueDef d).val.Evalb ![r, code] := value_total d step code
example (code : V) : Seq (history d step code) ∧ lh (history d step code) = code + 1 :=
  ⟨history_seq d step code, history_length d step code⟩
example : value d step (0 : V) = 0 := value_zero d step
example (code : V) : value d step (code + 1) = step (history d step code) (code + 1) :=
  value_succ d step code
example (code : V) : znth (history d step code) (code + 1) = 0 := by
  rw [history_lookup]
  simp
end

#print axioms history_defined
#print axioms history_defined_delta
#print axioms value_defined
#print axioms value_defined_delta
#print axioms history_total
#print axioms value_total
#print axioms history_seq
#print axioms history_length
#print axioms index_lt_length
#print axioms value_mem
#print axioms value_lt_history
#print axioms value_zero
#print axioms value_succ
#print axioms history_lookup_le
#print axioms history_lookup
