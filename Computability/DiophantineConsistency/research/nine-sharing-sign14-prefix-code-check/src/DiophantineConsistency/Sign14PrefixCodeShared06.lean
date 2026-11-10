import DiophantineConsistency.Sign14PrefixCodeShared05

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared30 : Code := (Code.add (shared21) (shared14))
def shared31 : Code := (Code.mul (shared23) (shared17))
def shared32 : Code := (Code.add (shared07) (shared31))
def shared33 : Code := (Code.mul (shared23) (shared23))
def shared34 : Code := (Code.sub (shared25) (shared27))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34

theorem shared30_interpret (p : Fin 4 → ℤ) :
    interpret p shared30 = SharingSeed14Degree124.shared30 p := by
  unfold shared30
  simp only [interpret, shared14_interpret, shared21_interpret] <;> rfl

theorem shared31_interpret (p : Fin 4 → ℤ) :
    interpret p shared31 = SharingSeed14Degree124.shared31 p := by
  unfold shared31
  simp only [interpret, shared17_interpret, shared23_interpret] <;> rfl

theorem shared32_interpret (p : Fin 4 → ℤ) :
    interpret p shared32 = SharingSeed14Degree124.shared32 p := by
  unfold shared32
  simp only [interpret, shared07_interpret, shared31_interpret] <;> rfl

theorem shared33_interpret (p : Fin 4 → ℤ) :
    interpret p shared33 = SharingSeed14Degree124.shared33 p := by
  unfold shared33
  simp only [interpret, shared23_interpret] <;> rfl

theorem shared34_interpret (p : Fin 4 → ℤ) :
    interpret p shared34 = SharingSeed14Degree124.shared34 p := by
  unfold shared34
  simp only [interpret, shared25_interpret, shared27_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared30_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared31_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared32_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared33_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared34_interpret
