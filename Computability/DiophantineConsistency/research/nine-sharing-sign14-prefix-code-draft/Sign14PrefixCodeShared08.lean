import DiophantineConsistency.Sign14PrefixCodeShared07

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared40 : Code := (Code.add (shared33) (shared26))
def shared41 : Code := (Code.mul (shared38) (shared39))
def shared42 : Code := (Code.mul ((Code.add (Code.var 6) (Code.one))) (shared41))
def shared43 : Code := (Code.mul (shared42) (shared42))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43

theorem shared40_interpret (p : Fin 4 → ℤ) :
    interpret p shared40 = SharingSeed14Degree124.shared40 p := by
  unfold shared40
  simp only [interpret, shared26_interpret, shared33_interpret] <;> rfl

theorem shared41_interpret (p : Fin 4 → ℤ) :
    interpret p shared41 = SharingSeed14Degree124.shared41 p := by
  unfold shared41
  simp only [interpret, shared38_interpret, shared39_interpret] <;> rfl

theorem shared42_interpret (p : Fin 4 → ℤ) :
    interpret p shared42 = SharingSeed14Degree124.shared42 p := by
  unfold shared42
  simp only [interpret, shared41_interpret] <;> rfl

theorem shared43_interpret (p : Fin 4 → ℤ) :
    interpret p shared43 = SharingSeed14Degree124.shared43 p := by
  unfold shared43
  simp only [interpret, shared42_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared40_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared41_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared42_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared43_interpret
