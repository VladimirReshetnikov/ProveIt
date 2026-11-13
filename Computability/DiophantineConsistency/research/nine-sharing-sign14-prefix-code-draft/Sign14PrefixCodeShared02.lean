import DiophantineConsistency.Sign14PrefixCodeShared01

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared10 : Code := (Code.add (shared06) ((Code.add (Code.var 3) (Code.one))))
def shared11 : Code := (Code.mul ((Code.add ((Code.add (Code.var 2) (Code.one))) ((Code.add (Code.var 3) (Code.one))))) (shared08))
def shared12 : Code := (Code.mul (shared08) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))
def shared13 : Code := (Code.mul ((Code.add (Code.var 8) (Code.one))) (shared12))
def shared14 : Code := (Code.sub (shared10) (shared01))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14

theorem shared10_interpret (p : Fin 4 → ℤ) :
    interpret p shared10 = SharingSeed14Degree124.shared10 p := by
  unfold shared10
  simp only [interpret, shared06_interpret] <;> rfl

theorem shared11_interpret (p : Fin 4 → ℤ) :
    interpret p shared11 = SharingSeed14Degree124.shared11 p := by
  unfold shared11
  simp only [interpret, shared08_interpret] <;> rfl

theorem shared12_interpret (p : Fin 4 → ℤ) :
    interpret p shared12 = SharingSeed14Degree124.shared12 p := by
  unfold shared12
  simp only [interpret, shared08_interpret] <;> rfl

theorem shared13_interpret (p : Fin 4 → ℤ) :
    interpret p shared13 = SharingSeed14Degree124.shared13 p := by
  unfold shared13
  simp only [interpret, shared12_interpret] <;> rfl

theorem shared14_interpret (p : Fin 4 → ℤ) :
    interpret p shared14 = SharingSeed14Degree124.shared14 p := by
  unfold shared14
  simp only [interpret, shared01_interpret, shared10_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared10_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared11_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared12_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared13_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared14_interpret
