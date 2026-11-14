import PA194SourceGateReduction
import PA194TargetGate
import PA194SourceHead1Syntax
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceGateTargetLink
open PA194SourceGateReduction PA194TargetGate PA194TargetCantor PA194TargetLeaves
open PA194SourceDiagonalPreservation PA194SourceFreshClose
open PA194SourceHead5Preservation PA194SourceHead1Syntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]





lemma gate_tail_eq (a b c : M) : gateTail a b c = separationTailValue a b c := by
  rfl
lemma gate_old_eq (a b c : M) :
    oldGate a b c = if c=a ∨ c=b then 0 else oldBundleValue a b c := by
  rfl
lemma checkGate_and_fresh (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    F checkGate ![a,b,c] = oldGate a b c + 1 := by
  rw [checkGate_model, gate_old_eq]
  simp [ha,hb]

lemma target_gate_from_tail (a b c : M) (ha : c ≠ a) (hb : c ≠ b)
    (htail : Provable (𝗣𝗔 : ArithmeticTheory) (translated (gateNeg (separationTailValue a b c)))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (oldBundleValue a b c)) := by
  have ht : Provable (𝗣𝗔 : ArithmeticTheory) (translated (gateNeg (gateTail a b c))) := by
    rw [gate_tail_eq]
    exact htail
  have hg := guarded_gate_if_tail a b c (fun _ _ => ht)
  rw [gate_old_eq, if_neg (by simp [ha,hb])] at hg
  exact hg

#print axioms target_gate_from_tail
#print axioms gate_old_eq
#print axioms checkGate_and_fresh
end models
end PA194SourceGateTargetLink
