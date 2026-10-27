import DiophantineConsistency.ArithmeticProofWordPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticProofWordPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCommandLeafPerm222 ArithmeticCommandStepPerm222 ArithmeticCommandRunPerm222
open ArithmeticProofWordPerm222

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (code : V) :
    ∃! word, rawWordDef.val.Evalb ![word,code] := rawWord_total code
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : rawWord (0 : V)=0 := rawWord_zero

-- Exact represented acceptance supplies the word and its all-stack contract.
example {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {code A : V}
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,A]) :
    ∃ word, rawWordDef.val.Evalb ![word,code] ∧ Contract word A :=
  ⟨rawWord code,by simp,check_contract h⟩

-- No global correctness or source-refutation premise is supplied separately.
example {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {code : V}
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) (top S : V) :
    ∃ word, refutationWordDef.val.Evalb ![word,code] ∧
      evalValue word (stateValue top S 0 0)=0 :=
  ⟨refutationWord code,by simp,refutationWord_halts code h top S⟩

#print axioms history_total
#print axioms rawWord_total
#print axioms history_lookup
#print axioms rawWord_succ
#print axioms good_definable
#print axioms prefixGood_definable
#print axioms good_succ
#print axioms good_all
#print axioms check_contract
#print axioms refutationWord_defined
#print axioms refutationWord_halts
end DiophantineConsistency.ArithmeticProofWordPerm222Checks
