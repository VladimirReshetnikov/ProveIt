import DiophantineConsistency.Sign14PrefixCodeShared03

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared20 : Code := (Code.mul (shared18) ((Code.add (Code.var 10) (Code.one))))
def shared21 : Code := (Code.add (shared20) ((Code.add ((Code.add (Code.var 11) (Code.one))) ((Code.add (Code.var 12) (Code.one))))))
def shared22 : Code := (Code.add (shared15) (shared11))
def shared23 : Code := (Code.add (shared18) (shared13))
def shared24 : Code := (Code.mul (Code.four) (shared23))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24

theorem shared20_interpret (p : Fin 4 → ℤ) :
    interpret p shared20 = SharingSeed14Degree124.shared20 p := by
  unfold shared20
  simp only [interpret, shared18_interpret] <;> rfl

theorem shared21_interpret (p : Fin 4 → ℤ) :
    interpret p shared21 = SharingSeed14Degree124.shared21 p := by
  unfold shared21
  simp only [interpret, shared20_interpret] <;> rfl

theorem shared22_interpret (p : Fin 4 → ℤ) :
    interpret p shared22 = SharingSeed14Degree124.shared22 p := by
  unfold shared22
  simp only [interpret, shared11_interpret, shared15_interpret] <;> rfl

theorem shared23_interpret (p : Fin 4 → ℤ) :
    interpret p shared23 = SharingSeed14Degree124.shared23 p := by
  unfold shared23
  simp only [interpret, shared13_interpret, shared18_interpret] <;> rfl

theorem shared24_interpret (p : Fin 4 → ℤ) :
    interpret p shared24 = SharingSeed14Degree124.shared24 p := by
  unfold shared24
  simp only [interpret, shared23_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared20_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared21_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared22_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared23_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared24_interpret
