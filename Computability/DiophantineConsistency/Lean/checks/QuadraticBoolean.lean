import DiophantineConsistency.QuadraticBoolean

open DiophantineConsistency

namespace QuadraticBooleanChecks

theorem zeroTest_correct (n out : ℕ) :
    out = (if n = 0 then 1 else 0) ↔ ∃ w : Fin 1 → ℕ,
      QuadraticBoolean.zeroTest.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => n) out) w) = 0 :=
  QuadraticBoolean.zeroTest.correct (withOutput (fun _ : Fin 1 => n) out)

theorem ifZero_correct (n yes no out : ℕ) :
    out = (if n = 0 then yes else no) ↔ ∃ w : Fin 2 → ℕ,
      QuadraticBoolean.ifZero.expression.eval
        (natAssignment (withOutput ![n,yes,no] out) w) = 0 :=
  QuadraticBoolean.ifZero.correct (withOutput ![n,yes,no] out)

theorem zero_branch_correct (yes no out : ℕ) :
    out = yes ↔ ∃ w : Fin 2 → ℕ, QuadraticBoolean.ifZero.expression.eval
      (natAssignment (withOutput ![0,yes,no] out) w) = 0 := by
  simpa using ifZero_correct 0 yes no out

theorem positive_branch_correct (n yes no out : ℕ) :
    out = no ↔ ∃ w : Fin 2 → ℕ, QuadraticBoolean.ifZero.expression.eval
      (natAssignment (withOutput ![n+1,yes,no] out) w) = 0 := by
  simpa using ifZero_correct (n+1) yes no out

example : QuadraticBoolean.zeroTest.witnessCount = 1 := rfl
example : QuadraticBoolean.ifZero.witnessCount = 2 := rfl
example : QuadraticBoolean.zeroTest.expression.binaryOps = 20 :=
  QuadraticBoolean.zeroTest_binaryOps
example : QuadraticBoolean.ifZero.expression.binaryOps = 32 :=
  QuadraticBoolean.ifZero_binaryOps

#print axioms QuadraticBoolean.zero_certificate_sound
#print axioms QuadraticBoolean.zero_certificate_complete
#print axioms QuadraticBoolean.exists_zero_certificate_iff
#print axioms QuadraticBoolean.zero_holds_iff
#print axioms QuadraticBoolean.conditional_holds_iff
#print axioms QuadraticBoolean.zeroTest_degree
#print axioms QuadraticBoolean.ifZero_degree
#print axioms QuadraticBoolean.zeroTest_binaryOps
#print axioms QuadraticBoolean.ifZero_binaryOps
#print axioms zeroTest_correct
#print axioms ifZero_correct
#print axioms zero_branch_correct
#print axioms positive_branch_correct

end QuadraticBooleanChecks
