import DiophantineConsistency.ArithmeticCommandWordPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandWordPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (z : V) : ∃! out, tailDef.val.Evalb ![out,z] := tail_total z
example (c y x r : V) : tailValue (cantor (c+3) (cantor y (cantor x r))) = r :=
  tail_ax c y x r
example : tailValue (0 : ℕ) = 0 := by
  rw [tail_nat]; rfl
example (cmd : EnumPerm.Cmd) (r : ℕ) : tailValue (EnumPerm.pack cmd r) = r :=
  tail_pack_nat cmd r
example (z : ℕ) : tailValue z = (EnumPerm.decode z).2 := tail_nat z

#print axioms tail_defined
#print axioms tail_total
#print axioms tail_le
#print axioms tail_nip
#print axioms tail_drop
#print axioms tail_mp
#print axioms tail_ax
#print axioms tail_pack_nat
#print axioms tail_nat
end DiophantineConsistency.ArithmeticCommandWordPerm222Checks
