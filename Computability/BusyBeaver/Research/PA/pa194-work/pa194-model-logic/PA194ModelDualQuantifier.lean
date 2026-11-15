import PA194ModelBinderAllocationShift
import PA194ModelSimTruthNeg
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance dualQuantifierZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance dualQuantifierOne : One M := ⟨F oneCode Fin.elim0⟩
local instance dualQuantifierAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance dualQuantifierMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance dualQuantifierLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance dualQuantifierIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem doubleNegationIntroduction (a : M) :
    TargetProvable (impValue a (negValue (negValue a))) := by
  let ha : Ctx [negValue a,a] a := .assumption (by simp)
  let hn : Ctx [negValue a,a] (negValue a) := .assumption (by simp)
  exact (Ctx.mp ha hn).deduction.deduction.empty

def TargetDual (a n : M) : Prop :=
    TargetProvable (impValue n (negValue a)) ∧ TargetProvable (impValue (negValue a) n)

theorem targetDual_all (d a n : M) (h : TargetDual a n) :
    TargetDual (allValue d a) (exValue d n) := by
  obtain ⟨h1,h2⟩ := h
  have ha : TargetProvable (impValue a (negValue n)) :=
    imp_trans (doubleNegationIntroduction a) (contrapose h1)
  have hb : TargetProvable (impValue (negValue n) a) :=
    imp_trans (contrapose h2) (doubleNegationElimination a)
  constructor
  · exact contrapose (liftImp d ha)
  · exact contrapose (liftImp d hb)

theorem targetDual_ex (d a n : M) (h : TargetDual a n) :
    TargetDual (exValue d a) (allValue d n) := by
  obtain ⟨h1,h2⟩ := h
  constructor
  · exact imp_trans (liftImp d h1) (doubleNegationIntroduction (allValue d (negValue a)))
  · exact imp_trans (doubleNegationElimination (allValue d (negValue a))) (liftImp d h2)

theorem targetDual_and (a n b m : M) (ha : TargetDual a n) (hb : TargetDual b m) :
    TargetDual (conjValue a b) (impValue (negValue n) m) := by
  obtain ⟨ha1,ha2⟩ := ha
  obtain ⟨hb1,hb2⟩ := hb
  constructor
  · let A := impValue (negValue n) m
    let C := conjValue a b
    let hx : Ctx [C,A] A := .assumption (by simp)
    let hc : Ctx [C,A] C := .assumption (by simp)
    let hna : Ctx (n :: [C,A]) n := .assumption (by simp)
    let hca := hc.andLeft.up n
    let hcontra := Ctx.mp hca (Ctx.mp hna (.closed ha1))
    let hnotn : Ctx [C,A] (negValue n) := hcontra.deduction
    let hm : Ctx [C,A] m := Ctx.mp hnotn hx
    let hnb : Ctx [C,A] (negValue b) := Ctx.mp hm (.closed hb1)
    exact (Ctx.mp hc.andRight hnb).deduction.deduction.empty
  · let C := negValue (conjValue a b)
    let hc : Ctx [negValue n,C] C := .assumption (by simp)
    let hn : Ctx [negValue n,C] (negValue n) := .assumption (by simp)
    let ha' : Ctx [negValue n,C] a := (Ctx.mp hn (.closed (contrapose ha2))).dne
    let hq : Ctx (b :: [negValue n,C]) b := .assumption (by simp)
    let hconj := Ctx.andIntro (ha'.up b) hq
    let hcontr := Ctx.mp hconj (hc.up b)
    let hnotb : Ctx [negValue n,C] (negValue b) := hcontr.deduction
    exact (Ctx.mp hnotb (.closed hb2)).deduction.deduction.empty

theorem targetDual_or (a n b m : M) (ha : TargetDual a n) (hb : TargetDual b m) :
    TargetDual (impValue (negValue a) b) (conjValue n m) := by
  obtain ⟨ha1,ha2⟩ := ha
  obtain ⟨hb1,hb2⟩ := hb
  constructor
  · let A := impValue (negValue a) b
    let C := conjValue n m
    let hc : Ctx [A,C] C := .assumption (by simp)
    let hA : Ctx [A,C] A := .assumption (by simp)
    let hna : Ctx [A,C] (negValue a) := Ctx.mp hc.andLeft (.closed ha1)
    let hnb : Ctx [A,C] (negValue b) := Ctx.mp hc.andRight (.closed hb1)
    exact (Ctx.mp (Ctx.mp hna hA) hnb).deduction.deduction.empty
  · let h : Ctx [negValue (impValue (negValue a) b)]
      (negValue (impValue (negValue a) b)) := .assumption (by simp)
    let hn : Ctx [negValue (impValue (negValue a) b)] n := Ctx.mp h.negImpLeft (.closed ha2)
    let hm : Ctx [negValue (impValue (negValue a) b)] m := Ctx.mp h.negImpRight (.closed hb2)
    exact (Ctx.andIntro hn hm).deduction.empty

def TranslationDual (p bound free base reserve : M) : Prop :=
  TargetDual (F fixedFormulaTranslation ![p,bound,free,base,reserve])
    (F fixedFormulaTranslation ![neg M6.PA.RelationalSource.language p,bound,free,base,reserve])

theorem translationDual_all (p bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (ih : TranslationDual p (pair base bound+1) free (base+1) reserve) :
    TranslationDual (^∀ p) bound free base reserve := by
  unfold TranslationDual at ih ⊢
  rw [neg_all hp,fixedFormulaTranslation_all p bound free base reserve hp,
    fixedFormulaTranslation_ex (neg M6.PA.RelationalSource.language p) bound free base reserve hp.neg]
  exact targetDual_all base _ _ ih

theorem translationDual_ex (p bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (ih : TranslationDual p (pair base bound+1) free (base+1) reserve) :
    TranslationDual (^∃ p) bound free base reserve := by
  unfold TranslationDual at ih ⊢
  rw [neg_ex hp,fixedFormulaTranslation_ex p bound free base reserve hp,
    fixedFormulaTranslation_all (neg M6.PA.RelationalSource.language p) bound free base reserve hp.neg]
  exact targetDual_ex base _ _ ih

theorem translationDual_positiveAtom (r v bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    TranslationDual (^rel (2 : M) r v) bound free base reserve := by
  unfold TranslationDual TargetDual
  rw [neg_rel hr hv,fixedFormulaTranslation_atom_polarity r v bound free base reserve hr hv]
  exact ⟨imp_refl _,imp_refl _⟩

theorem translationDual_negativeAtom (r v bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    TranslationDual (^nrel (2 : M) r v) bound free base reserve := by
  unfold TranslationDual TargetDual
  rw [neg_nrel hr hv,fixedFormulaTranslation_atom_polarity r v bound free base reserve hr hv]
  exact ⟨doubleNegationIntroduction _,doubleNegationElimination _⟩

theorem translationDual_verum (bound free base reserve : M) :
    TranslationDual (^⊤ : M) bound free base reserve := by
  unfold TranslationDual TargetDual
  rw [neg_verum,fixedFormulaTranslation_verum,fixedFormulaTranslation_falsum]
  constructor
  · exact explosion _
  · let h : Ctx [negValue (0 : M)] (negValue 0) := .assumption (by simp)
    exact (Ctx.mp (.closed sequentTruth_zero) h).deduction.empty

theorem translationDual_falsum (bound free base reserve : M) :
    TranslationDual (^⊥ : M) bound free base reserve := by
  unfold TranslationDual TargetDual
  rw [neg_falsum,fixedFormulaTranslation_falsum,fixedFormulaTranslation_verum]
  exact ⟨tp_mp (imp_refl (1 : M)) (imp_k (negValue 1) 0),
    tp_mp sequentTruth_zero (imp_k 0 (negValue 1))⟩

#print axioms translationDual_positiveAtom
#print axioms translationDual_negativeAtom
#print axioms translationDual_verum
#print axioms translationDual_falsum
theorem translationDual_and (p q bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q)
    (ihp : TranslationDual p bound free base reserve)
    (ihq : TranslationDual q bound free base reserve) :
    TranslationDual (p ^⋏ q) bound free base reserve := by
  unfold TranslationDual at ihp ihq ⊢
  rw [neg_and hp hq,fixedFormulaTranslation_and p q bound free base reserve hp hq,
    fixedFormulaTranslation_or (neg M6.PA.RelationalSource.language p)
      (neg M6.PA.RelationalSource.language q) bound free base reserve hp.neg hq.neg]
  exact targetDual_and _ _ _ _ ihp ihq

theorem translationDual_or (p q bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q)
    (ihp : TranslationDual p bound free base reserve)
    (ihq : TranslationDual q bound free base reserve) :
    TranslationDual (p ^⋎ q) bound free base reserve := by
  unfold TranslationDual at ihp ihq ⊢
  rw [neg_or hp hq,fixedFormulaTranslation_or p q bound free base reserve hp hq,
    fixedFormulaTranslation_and (neg M6.PA.RelationalSource.language p)
      (neg M6.PA.RelationalSource.language q) bound free base reserve hp.neg hq.neg]
  exact targetDual_or _ _ _ _ ihp ihq

#print axioms targetDual_and
#print axioms targetDual_or
#print axioms translationDual_and
#print axioms translationDual_or
#print axioms doubleNegationIntroduction
#print axioms targetDual_all
#print axioms targetDual_ex
#print axioms translationDual_all
#print axioms translationDual_ex
end models
end PA194ModelLogic
