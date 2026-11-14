import PA194SourceDiagonalPreservation
import PA194SourceHead1Syntax
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceGateReduction
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




lemma membership_vacuity (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (memSource a b) (allSource c (memSource a b)))) := by
  have hnz := imp_nonzero_left (memSource a b) (allSource c (memSource a b)) (memSource_nonzero a b)
  rw [imp_code _ _ hnz, universal_code c (memSource a b), membership_code]
  let P : Bootstrapping.Formula M ℒₒᵣ := bitFormula a b
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close c 0 P.val, by
    simpa using PA194InternalFormulaClose.close_wellformed c 0 P.val P.isSemiformula⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) ((P 🡒 ∀⁰ Q).val)
  have hf : renameFormula replaceGraph replaceMap replaceGraph_correct (pair c (c+1)) P.val = P.val := by
    change renameFormula replaceGraph replaceMap replaceGraph_correct (pair c (c+1)) (bitFormula a b).val = _
    rw [rename_bit]
    simp [ha,hb,P]
  have hclose : Q.val = P.val := formula_close_of_fixed c (c+1) 0 P.val (ne_of_lt (lt_add_one c)) P.isSemiformula hf
  have hfree : Q.free = P.shift := unbound_free P Q hclose
  apply (tprovable_iff_provable).mp
  apply Nonempty.intro
  apply TProof.generalizeAux
  rw [hfree]
  exact C_id

lemma old_gate_reduction (a b c tail : M) (ha : c ≠ a) (hb : c ≠ b)
    (htail : Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource tail 1))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (impSource (impSource (memSource a b) (allSource c (memSource a b))) tail) 1)) := by
  classical
  let V := impSource (memSource a b) (allSource c (memSource a b))
  have hV : Provable (𝗣𝗔 : ArithmeticTheory) (translated V) := membership_vacuity a b c ha hb
  have hVnz : V ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero a b)
  have hinner : impSource V tail ≠ 0 := imp_nonzero_left _ _ hVnz
  have hout : impSource (impSource V tail) 1 ≠ 0 := imp_nonzero_left _ _ hinner
  have htailnz : impSource tail 1 ≠ 0 := imp_nonzero_right tail 1 (by norm_num)
  change Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (impSource V tail) 1))
  rw [imp_code _ _ hout, imp_code _ _ hinner]
  rw [imp_code _ _ htailnz] at htail
  let P : Bootstrapping.Formula M ℒₒᵣ := ⟨translated V,(fixed_all_wf V).1⟩
  let Q : Bootstrapping.Formula M ℒₒᵣ := ⟨translated tail,(fixed_all_wf tail).1⟩
  let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1,(fixed_all_wf 1).1⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) (((P 🡒 Q) 🡒 D).val)
  have hp : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ P := (tprovable_iff_provable).mpr hV
  have hqd : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ Q 🡒 D := (tprovable_iff_provable).mpr htail
  apply (tprovable_iff_provable).mp
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hi : [P 🡒 Q] ⊢[(𝗣𝗔 : ArithmeticTheory).internalize M]! P 🡒 Q := FiniteContext.byAxm (by simp)
  have hp' : [P 🡒 Q] ⊢[(𝗣𝗔 : ArithmeticTheory).internalize M]! P := FiniteContext.of hp.some
  have hqd' : [P 🡒 Q] ⊢[(𝗣𝗔 : ArithmeticTheory).internalize M]! Q 🡒 D := FiniteContext.of hqd.some
  exact hqd' ⨀ (hi ⨀ hp')

noncomputable def gateNeg (p : M) := impSource p 1
noncomputable def gateConj (p q : M) := gateNeg (impSource p (gateNeg q))
noncomputable def gatePoint (b c : M) := impSource c (memSource c b)
noncomputable def gateSeparation (a b c : M) :=
  allSource b (gateConj (impSource (memSource a b) (gatePoint b c)) (impSource (memSource c b) c))
noncomputable def gateTail (a b c : M) := allSource c (impSource (gateSeparation a b c) (gateNeg (gatePoint b c)))
noncomputable def oldGate (a b c : M) :=
  if c=a ∨ c=b then 0 else gateNeg (impSource (impSource (memSource a b) (allSource c (memSource a b))) (gateTail a b c))

lemma guarded_gate_if_tail (a b c : M)
    (htail : c ≠ a → c ≠ b → Provable (𝗣𝗔 : ArithmeticTheory) (translated (gateNeg (gateTail a b c)))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (oldGate a b c)) := by
  classical
  by_cases hh : c=a ∨ c=b
  · simp only [oldGate, if_pos hh]
    exact zero_provable
  · have ha : c ≠ a := fun h => hh (Or.inl h)
    have hb : c ≠ b := fun h => hh (Or.inr h)
    simp only [oldGate, if_neg hh,gateNeg]
    exact old_gate_reduction a b c (gateTail a b c) ha hb (htail ha hb)

#print axioms guarded_gate_if_tail
#print axioms membership_vacuity
#print axioms old_gate_reduction
end models
end PA194SourceGateReduction
