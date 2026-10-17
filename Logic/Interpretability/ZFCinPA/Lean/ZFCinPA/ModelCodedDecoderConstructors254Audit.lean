import ZFCinPA.ModelCodedDecoderConstructors254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.cantor_zero_iff
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.impCode_zero_iff
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_positive
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_imp
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_imp_total
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_mem
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_all
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_eq
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_one

example (a b : V) : 4*cantor a b = 0 ↔ a = 0 ∧ b = 0 := impCode_zero_iff a b
example (a b : V) (h : ¬(a = 0 ∧ b = 0)) :
    decode (4*cantor a b) = imp ℒₛₑₜ (decode a) (decode b) := decode_imp a b h
example (a b : V) : decode (4*cantor a b) =
    if a = 0 ∧ b = 0 then zeroFormula else imp ℒₛₑₜ (decode a) (decode b) := decode_imp_total a b
example : decode (4*cantor (0 : V) 0) = zeroFormula := by
  rw [decode_imp_total,if_pos ⟨rfl,rfl⟩]
example (a b : V) : decode (4*cantor a b+1) = atomCode 1 a b := decode_mem a b
example (a b : V) : decode (4*cantor a b+2) = namedAll ℒₛₑₜ a (decode b) := decode_all a b
example (a b : V) : decode (4*cantor a b+3) = atomCode 0 a b := decode_eq a b
example : decode (1 : V) = atomCode 1 0 0 := decode_one
example (a b : Nat) (h : ¬(a = 0 ∧ b = 0)) :
    decode (Code254.wim a b) = imp ℒₛₑₜ (decode a) (decode b) := by
  have hh := decode_imp a b h
  rw [←numeral_four_eq_four] at hh
  simpa only [Nat.numeral_eq,cantor_nat,Code254.wim] using hh
example (a b : Nat) : decode (Code254.wel a b) = atomCode 1 a b := by
  have hh := decode_mem a b
  rw [←numeral_four_eq_four] at hh
  simpa only [Nat.numeral_eq,cantor_nat,Code254.wel] using hh
example (a b : Nat) : decode (Code254.wal a b) = namedAll ℒₛₑₜ a (decode b) := by
  have hh := decode_all a b
  rw [←numeral_four_eq_four,←numeral_two_eq_two] at hh
  simpa only [Nat.numeral_eq,cantor_nat,Code254.wal] using hh
example (a b : Nat) : decode (Code254.weq a b) = atomCode 0 a b := by
  have hh := decode_eq a b
  rw [←numeral_four_eq_four,←numeral_three_eq_three] at hh
  simpa only [Nat.numeral_eq,cantor_nat,Code254.weq] using hh
