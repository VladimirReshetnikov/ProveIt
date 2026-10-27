import DiophantineConsistency.ArithmeticCommandLeafPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandLeafPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
open ArithmeticCommandStepPerm222 ArithmeticCommandAppendPerm222 ArithmeticCommandRunPerm222
open ArithmeticCommandBlockPerm222 ArithmeticCommandLeafPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚷₁-Relation (Contract (V := V)) := contract_definable
example (S : V) :
    evalValue (appendValue (nipsWord 1) (dropWord (nipsWord 2)))
      (stateValue 0 (pushL [0,1] S) 0 0)=someState 0 S 0 1 := by
  simpa using select_entry ([] : List V) 0 [] 1 0 0 S
    (by simp) (by simp) (by simp) (by simp) (by simp)
example (top S : V) :
    evalValue (leafWord 6 (0 : V) 0 0 0) (stateValue top S 0 0)=someState (rho6 0 0) S 0 0 :=
  eval_leaf 6 0 0 0 0 _ [_,_,_,_,_] _ (by simp) rfl rfl rfl top S
example (a b : V) : Contract (leafWord 6 a 0 b 0) (rho6 a b) := leaf6 a b
example (a b c : V) : Contract (leafWord 7 a b c 0) (ArithmeticTemplates222.growG a b c) :=
  leaf7 a b c
example (u b c : V) : Contract (leafWord 8 u b c u) (rho8 u b c u) := leaf8 u b c u le_rfl
example (u b c : V) : Contract (leafWord 9 u b c u) (wal u 0) := leaf9 u b c u le_rfl
example (b : V) (hb : (0 : V)≠b) :
    Contract (bundleWord 1 b 0) (ArithmeticSeedTemplates222.bundle222 1 b 0) :=
  bundle_contract 1 b 0 (by simp) hb
example : Contract (bundleWord (0 : V) 0 1) (ArithmeticSeedTemplates222.bundle222 0 0 1) :=
  bundle_contract 0 0 1 (by simp) (by simp)
example : Contract (bundleWord (1 : V) 1 0) (ArithmeticSeedTemplates222.bundle222 1 1 0) :=
  bundle_contract 1 1 0 (by simp) (by simp)
example (a b : V) : Contract (bundleWord a b a) 0 := bundle_collision a b a (Or.inl rfl)
example (a b : V) : Contract (bundleWord a b b) 0 := bundle_collision a b b (Or.inr rfl)
example (word : V) (h : Contract word 1) (top S : V) :
    evalValue (appendValue word terminatorWord) (stateValue top S 0 0)=0 :=
  false_target_halts word h top S

#print axioms contract_definable
#print axioms truth_contract
#print axioms select_entry
#print axioms eval_leaf
#print axioms leaf1
#print axioms leaf2
#print axioms leaf3
#print axioms leaf4
#print axioms leaf5
#print axioms leaf6
#print axioms leaf7
#print axioms leaf8
#print axioms leaf9
#print axioms eval_bundle
#print axioms bundle_contract
#print axioms bundle_collision
#print axioms eval_terminator
#print axioms false_target_halts
end DiophantineConsistency.ArithmeticCommandLeafPerm222Checks
