import DiophantineConsistency.Sign14PrefixCodeShared08

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def row00 : Code := (Code.sub (shared41) ((Code.mul (shared40) ((Code.mul (shared17) (shared17))))))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43

theorem row00_interpret (p : Fin 4 → ℤ) :
    interpret p row00 = SharingSeed14Degree124.row00 p := by
  unfold row00
  simp only [interpret, shared17_interpret, shared40_interpret, shared41_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.row00_interpret
