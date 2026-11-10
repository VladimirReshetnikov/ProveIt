import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
def row01 : Code := (Code.sub ((Code.sub ((Code.mul (shared36) (shared36))) ((Code.mul (shared29) ((Code.add (shared29) ((Code.add ((Code.add (Code.var 11) (Code.one))) ((Code.add (Code.var 12) (Code.one))))))))))) (Code.one))

attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43

theorem row01_interpret (p : Fin 4 → ℤ) :
    interpret p row01 = SharingSeed14Degree124.row01 p := by
  unfold row01
  simp only [interpret, shared29_interpret, shared36_interpret] <;> rfl

end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.row01_interpret
