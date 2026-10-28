import DiophantineConsistency.ArithmeticProofWordRowPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticProofWordRowPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandLeafPerm222 ArithmeticProofWordRowPerm222

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tag payload u v : V) :
    ∃! word, rowDef.val.Evalb ![word,tag,payload,u,v] := row_total tag payload u v

-- The actual tag10 has no dominance premise, even when u is above a.
example {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b c : V) :
    Contract (rowValue 10 (cantor a (cantor b (cantor c (a+1)))) 0 0)
      (ArithmeticTemplates254.rho8 a b c (a+1)) := by
  simpa [rowValue] using rho8_contract a b c (a+1)

-- Data at an invalid tag still has an exact numeric result.
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (payload u v : V) :
    rowValue 12 payload u v=0 := by simp [rowValue]

-- The full row client keeps arbitrary child words and their all-stack contracts.
example {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tag payload u v p q : V)
    (hp : u≠0 → Contract p (u-1)) (hq : v≠0 → Contract q (v-1))
    (hr : ArithmeticRow222.rowKernel tag payload u v≠0) :
    Contract (rowValue tag payload p q) (ArithmeticRow222.rowKernel tag payload u v-1) :=
  row_contract tag payload u v p q hp hq hr

#print axioms rho8_contract
#print axioms eval_genCircuit
#print axioms eval_bundleCircuit
#print axioms row_defined
#print axioms row_total
#print axioms row_contract
end DiophantineConsistency.ArithmeticProofWordRowPerm222Checks
