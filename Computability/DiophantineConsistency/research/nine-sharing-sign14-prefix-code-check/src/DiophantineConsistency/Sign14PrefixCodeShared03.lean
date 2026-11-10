import DiophantineConsistency.Sign14PrefixCodeShared02

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared15 : Code := (Code.mul (shared03) (shared12))
def shared16 : Code := (Code.mul ((Code.add ((Code.add (Code.var 11) (Code.one))) ((Code.add (Code.var 12) (Code.one))))) (shared13))
def shared17 : Code := (Code.add (shared16) ((Code.add (Code.var 11) (Code.one))))
def shared18 : Code := (Code.mul (shared05) (shared13))
def shared19 : Code := (Code.mul (shared17) ((Code.add (Code.var 7) (Code.one))))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19

theorem shared15_interpret (p : Fin 4 → ℤ) :
    interpret p shared15 = SharingSeed14Degree124.shared15 p := by
  unfold shared15
  simp only [interpret, shared03_interpret, shared12_interpret] <;> rfl

theorem shared16_interpret (p : Fin 4 → ℤ) :
    interpret p shared16 = SharingSeed14Degree124.shared16 p := by
  unfold shared16
  simp only [interpret, shared13_interpret] <;> rfl

theorem shared17_interpret (p : Fin 4 → ℤ) :
    interpret p shared17 = SharingSeed14Degree124.shared17 p := by
  unfold shared17
  simp only [interpret, shared16_interpret] <;> rfl

theorem shared18_interpret (p : Fin 4 → ℤ) :
    interpret p shared18 = SharingSeed14Degree124.shared18 p := by
  unfold shared18
  simp only [interpret, shared05_interpret, shared13_interpret] <;> rfl

theorem shared19_interpret (p : Fin 4 → ℤ) :
    interpret p shared19 = SharingSeed14Degree124.shared19 p := by
  unfold shared19
  simp only [interpret, shared17_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared15_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared16_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared17_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared18_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared19_interpret
