module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.EndpointTraceAdequacy
public import M6PA.Scheduler.ActualProofCodeTable
public import Mathlib.Data.List.GetD
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualTableCoding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Internal table entry convention, not Foundation's generic Option encoding:
zero rejects, while a proof with conclusion zero is represented by one. -/
def optionCode : Option Nat → Nat
  | none => 0
  | some a => a+1

theorem optionCode_injective : Function.Injective optionCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [optionCode]

/-- Reuse the existing exact HFS prefix encoder; Source Cantor proof trees
remain a separate code. -/
noncomputable def encodeTable (xs : List (Option Nat)) : Nat :=
  HaltingFormula.encodePrefix xs.length (fun i => optionCode (xs.getD i none))

theorem len_encodePrefix (n : Nat) (f : Nat → Nat) :
    len (HaltingFormula.encodePrefix n f) = n := by
  induction n generalizing f with
  | zero => simp [HaltingFormula.encodePrefix]
  | succ n ih => simp [HaltingFormula.encodePrefix,ih]

@[simp] theorem len_encodeTable (xs : List (Option Nat)) :
    len (encodeTable xs) = xs.length := len_encodePrefix _ _

theorem nth_encodeTable (xs : List (Option Nat)) (i : Nat) :
    nth (encodeTable xs) i = optionCode (xs.getD i none) := by
  by_cases hi : i<xs.length
  · exact HaltingFormula.nth_encodePrefix _ _ _ hi
  · have hzero : nth (encodeTable xs) i=0 := nth_lt_len (by
      change len (encodeTable xs)=i ∨ len (encodeTable xs)<i
      rw [len_encodeTable]
      omega)
    rw [hzero,List.getD_eq_default xs none (Nat.le_of_not_gt hi)]
    rfl

open NativeCalculus.ActualBasis.Code in
theorem nth_encoded_table (bound fuel n : Nat) (hn : n≤bound) :
    nth (encodeTable (table bound fuel)) n = optionCode (check fuel n) := by
  rw [nth_encodeTable,table_lookup bound fuel n hn]

#print axioms optionCode_injective
#print axioms nth_encodeTable
#print axioms nth_encoded_table
end M6.PA.ActualTableCoding

