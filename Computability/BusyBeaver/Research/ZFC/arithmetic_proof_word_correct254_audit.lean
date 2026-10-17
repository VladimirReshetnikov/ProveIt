import BusyBeaver.ZFC.ArithmeticProofWordCorrect254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticRow254 ArithmeticHistory254
open ArithmeticCommandStep254 ArithmeticCommandRun254
open ArithmeticProofWordRow254 ArithmeticProofWord254 ArithmeticProofWordContract254
open ArithmeticProofWordCorrect254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254.row_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254.good_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254.good_all
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254.accepted_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254.compiled_contract
example (code : V) : Good code := good_all code
example (raw : V) (h : PrefixGood raw) : Good (raw + 1) := good_succ raw h
example (code : V) (hv : value code ≠ 0) :
    Contract (rawWord code) (value code - 1) := accepted_contract code hv
example (code top stack : V) (hv : value code ≠ 0) :
    evalValue (rawWord code) (stateValue top stack 0 0) = 0 ∨
    evalValue (rawWord code) (stateValue top stack 0 0) =
      someState (value code - 1) stack 0 0 := accepted_contract code hv top stack
example (code top stack : V) (hv : value code ≠ 0) :
    evalValue (compiledWord code) (stateValue top stack 0 0) = 0 ∨
    evalValue (compiledWord code) (stateValue top stack 0 0) =
      someState (value code - 1) stack 0 0 := compiled_contract code hv top stack
example (code minor stack : V) (hv : value code ≠ 0) :
    evalValue (rawWord code) (stateValue 0 (cantor minor stack) 0 0) = 0 ∨
    evalValue (rawWord code) (stateValue 0 (cantor minor stack) 0 0) =
      someState (value code - 1) (cantor minor stack) 0 0 :=
  accepted_contract code hv 0 (cantor minor stack)
example (tag payload u v p q : V)
    (hp : u ≠ 0 → Contract p (u - 1)) (hq : v ≠ 0 → Contract q (v - 1))
    (hr : rowKernel tag payload u v ≠ 0) :
    Contract (rowValue tag payload p q) (rowKernel tag payload u v - 1) :=
  row_contract tag payload u v p q hp hq hr
example (p q b x : V) (hp : Contract p x) (hq : Contract q (wim x b)) :
    Contract (rowValue 1 (cantor b 0) p q) b := by
  have hg : MPGate b (x+1) (wim x b+1) :=
    ⟨x, by simp, wim x b, by simp, rfl, rfl, rfl⟩
  have hc := row_contract (1 : V) (cantor b 0) (x+1) (wim x b+1) p q
    (by intro _; simpa using hp) (by intro _; simpa using hq)
    (by simp [rowKernel, mpValue, hg])
  simpa [rowKernel, mpValue, hg] using hc
example (p i h : V) (hp : Contract p h) :
    Contract (rowValue 2 (cantor i 0) p 0) (wal i h) := by
  have hc := row_contract (2 : V) (cantor i 0) (h+1) (0 : V) p 0
    (by intro _; simpa using hp) (by simp)
    (by simp [rowKernel, genValue])
  simpa [rowKernel, genValue] using hc
example (a b c : V) (h1 : c ≠ a) (h2 : c ≠ b) :
    Contract (rowValue 11 (cantor a (cantor b c)) 0 0)
      (ArithmeticTemplates254.bundle a b c) := by
  have hc := row_contract (11 : V) (cantor a (cantor b c)) 0 0 0 0
    (by simp) (by simp) (by simp [rowKernel, h1, h2])
  simpa [rowKernel, h1, h2] using hc
example : Good (0 : V) := good_all 0
example (code : V) (hi : value code = 0) : Good code := Or.inl hi
example (code : V) (hv : value code = (1 : V) + 1) : Contract (rawWord code) 1 := by
  have hc := accepted_contract code (by rw [hv]; simp)
  simpa [hv] using hc
