import DiophantineConsistency.Sign14PrefixCodeShared06

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def shared35 : Code := (Code.mul ((Code.mul ((Code.add (Code.var 5) (Code.one))) ((Code.add (Code.var 5) (Code.one))))) (shared34))
def shared36 : Code := (Code.sub (shared30) (shared27))
def shared37 : Code := (Code.sub (shared35) (shared17))
def shared38 : Code := (Code.add (shared32) (shared28))
def shared39 : Code := (Code.add (shared38) (Code.two))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39

theorem shared35_interpret (p : Fin 4 → ℤ) :
    interpret p shared35 = SharingSeed14Degree124.shared35 p := by
  unfold shared35
  simp only [interpret, shared34_interpret] <;> rfl

theorem shared36_interpret (p : Fin 4 → ℤ) :
    interpret p shared36 = SharingSeed14Degree124.shared36 p := by
  unfold shared36
  simp only [interpret, shared27_interpret, shared30_interpret] <;> rfl

theorem shared37_interpret (p : Fin 4 → ℤ) :
    interpret p shared37 = SharingSeed14Degree124.shared37 p := by
  unfold shared37
  simp only [interpret, shared17_interpret, shared35_interpret] <;> rfl

theorem shared38_interpret (p : Fin 4 → ℤ) :
    interpret p shared38 = SharingSeed14Degree124.shared38 p := by
  unfold shared38
  simp only [interpret, shared28_interpret, shared32_interpret] <;> rfl

theorem shared39_interpret (p : Fin 4 → ℤ) :
    interpret p shared39 = SharingSeed14Degree124.shared39 p := by
  unfold shared39
  simp only [interpret, shared38_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.shared35_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared36_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared37_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared38_interpret
#print axioms DiophantineConsistency.Sign14PrefixCode.shared39_interpret
