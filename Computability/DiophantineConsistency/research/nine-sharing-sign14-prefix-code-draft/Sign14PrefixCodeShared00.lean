import DiophantineConsistency.Sign14PrefixReflection

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared00 : Code := (Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) (Code.port 3))
def shared01 : Code := (Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add (Code.var 2) (Code.one))))
def shared02 : Code := (Code.mul (Code.var 9) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))
def shared03 : Code := (Code.sub ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add (Code.var 2) (Code.one))))
def shared04 : Code := (Code.add (Code.port 2) (shared00))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04

theorem shared00_interpret (p : Fin 4 → ℤ) :
    interpret p shared00 = SharingSeed14Degree124.shared00 p := by
  unfold shared00
  simp only [interpret] <;> rfl

theorem shared01_interpret (p : Fin 4 → ℤ) :
    interpret p shared01 = SharingSeed14Degree124.shared01 p := by
  unfold shared01
  simp only [interpret] <;> rfl

theorem shared02_interpret (p : Fin 4 → ℤ) :
    interpret p shared02 = SharingSeed14Degree124.shared02 p := by
  unfold shared02
  simp only [interpret] <;> rfl

theorem shared03_interpret (p : Fin 4 → ℤ) :
    interpret p shared03 = SharingSeed14Degree124.shared03 p := by
  unfold shared03
  simp only [interpret] <;> rfl

theorem shared04_interpret (p : Fin 4 → ℤ) :
    interpret p shared04 = SharingSeed14Degree124.shared04 p := by
  unfold shared04
  simp only [interpret, shared00_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared00_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared01_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared02_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared03_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared04_interpret
