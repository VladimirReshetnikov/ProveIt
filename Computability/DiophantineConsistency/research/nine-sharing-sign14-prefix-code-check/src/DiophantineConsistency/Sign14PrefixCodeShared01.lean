import DiophantineConsistency.Sign14PrefixCodeShared00

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared05 : Code := (Code.mul ((Code.add (Code.var 9) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))
def shared06 : Code := (Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))
def shared07 : Code := (Code.add (shared02) ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))))
def shared08 : Code := (Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))
def shared09 : Code := (Code.mul (shared04) ((Code.add (Code.var 1) (Code.one))))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09

theorem shared05_interpret (p : Fin 4 → ℤ) :
    interpret p shared05 = SharingSeed14Degree124.shared05 p := by
  unfold shared05
  simp only [interpret] <;> rfl

theorem shared06_interpret (p : Fin 4 → ℤ) :
    interpret p shared06 = SharingSeed14Degree124.shared06 p := by
  unfold shared06
  simp only [interpret] <;> rfl

theorem shared07_interpret (p : Fin 4 → ℤ) :
    interpret p shared07 = SharingSeed14Degree124.shared07 p := by
  unfold shared07
  simp only [interpret, shared02_interpret] <;> rfl

theorem shared08_interpret (p : Fin 4 → ℤ) :
    interpret p shared08 = SharingSeed14Degree124.shared08 p := by
  unfold shared08
  simp only [interpret] <;> rfl

theorem shared09_interpret (p : Fin 4 → ℤ) :
    interpret p shared09 = SharingSeed14Degree124.shared09 p := by
  unfold shared09
  simp only [interpret, shared04_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared05_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared06_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared07_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared08_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared09_interpret
