import DiophantineConsistency.Sign14PrefixCodeShared04

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared25 : Code := (Code.add (shared19) (shared14))
def shared26 : Code := (Code.add (shared24) (Code.three))
def shared27 : Code := (Code.add (shared22) (shared09))
def shared28 : Code := (Code.mul ((Code.add (Code.var 14) (Code.one))) (shared26))
def shared29 : Code := (Code.mul (shared18) (shared16))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29

theorem shared25_interpret (p : Fin 4 → ℤ) :
    interpret p shared25 = SharingSeed14Degree124.shared25 p := by
  unfold shared25
  simp only [interpret, shared14_interpret, shared19_interpret] <;> rfl

theorem shared26_interpret (p : Fin 4 → ℤ) :
    interpret p shared26 = SharingSeed14Degree124.shared26 p := by
  unfold shared26
  simp only [interpret, shared24_interpret] <;> rfl

theorem shared27_interpret (p : Fin 4 → ℤ) :
    interpret p shared27 = SharingSeed14Degree124.shared27 p := by
  unfold shared27
  simp only [interpret, shared09_interpret, shared22_interpret] <;> rfl

theorem shared28_interpret (p : Fin 4 → ℤ) :
    interpret p shared28 = SharingSeed14Degree124.shared28 p := by
  unfold shared28
  simp only [interpret, shared26_interpret] <;> rfl

theorem shared29_interpret (p : Fin 4 → ℤ) :
    interpret p shared29 = SharingSeed14Degree124.shared29 p := by
  unfold shared29
  simp only [interpret, shared16_interpret, shared18_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared25_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared26_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared27_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared28_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared29_interpret
