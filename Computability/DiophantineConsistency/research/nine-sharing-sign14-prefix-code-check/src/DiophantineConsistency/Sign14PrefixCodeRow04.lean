import DiophantineConsistency.Sign14PrefixCodeRow03

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def row04 : Code := (Code.sub ((Code.sub ((Code.mul (shared40) ((Code.mul ((Code.add (Code.var 5) (Code.one))) ((Code.add (Code.var 5) (Code.one))))))) (shared43))) (shared40))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43

theorem row04_interpret (p : Fin 4 → ℤ) :
    interpret p row04 = SharingSeed14Degree124.row04 p := by
  unfold row04
  simp only [interpret, shared40_interpret, shared43_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.row04_interpret
