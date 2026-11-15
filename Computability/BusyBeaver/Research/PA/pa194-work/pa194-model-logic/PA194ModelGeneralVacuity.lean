import PA194ModelFreshBoolean
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Target vacuity at arbitrary source-translation labels. -/
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
local instance generalVacZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance generalVacOne : One M := ⟨F oneCode Fin.elim0⟩
local instance generalVacAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance generalVacMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance generalVacLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance generalVacIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- The source translation is vacuous at an independently chosen target label. -/
noncomputable def GeneralVacuity (x e p : M) : Prop :=
  TargetProvable (impValue (F fixedFormulaTranslation ![p,simBound e,simFree e,simBase e,simReserve e])
    (allValue x (F fixedFormulaTranslation ![p,simBound e,simFree e,simBase e,simReserve e])))

noncomputable def simEnterBinder (e : M) : M :=
  pair (pair (simBase e) (simBound e)+1) (pair (simFree e) (pair (simBase e+1) (simReserve e)))

theorem simEnterBinder_fields (e : M) :
    simBound (simEnterBinder e) = pair (simBase e) (simBound e)+1 ∧
    simFree (simEnterBinder e) = simFree e ∧ simBase (simEnterBinder e) = simBase e+1 ∧
    simReserve (simEnterBinder e) = simReserve e := by
  simp [simEnterBinder,simBound,simFree,simBase,simReserve]

theorem generalVacuity_verum (x e : M) : GeneralVacuity x e (^⊤ : M) := by
  unfold GeneralVacuity
  rw [fixedFormulaTranslation_verum]
  exact tp_mp (tp_gen x sequentTruth_zero) (imp_k _ 0)

theorem generalVacuity_falsum (x e : M) : GeneralVacuity x e (^⊥ : M) := by
  unfold GeneralVacuity
  rw [fixedFormulaTranslation_falsum]
  exact explosion _

theorem generalVacuity_and (x e p q : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (h1 : GeneralVacuity x e p) (h2 : GeneralVacuity x e q) : GeneralVacuity x e (p ^⋏ q) := by
  unfold GeneralVacuity at h1 h2 ⊢
  rw [fixedFormulaTranslation_and p q _ _ _ _ hp hq]
  exact conjunctionVacuity x _ _ h1 h2

theorem generalVacuity_or (x e p q : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (h1 : GeneralVacuity x e p) (h2 : GeneralVacuity x e q) : GeneralVacuity x e (p ^⋎ q) := by
  unfold GeneralVacuity at h1 h2 ⊢
  rw [fixedFormulaTranslation_or p q _ _ _ _ hp hq]
  exact implicationVacuity x _ _ (negationVacuity x _ h1) h2

theorem generalVacuity_all (x e p : M) (hp : IsUFormula SourceL p)
    (h : GeneralVacuity x (simEnterBinder e) p) : GeneralVacuity x e (^∀ p) := by
  unfold GeneralVacuity at h ⊢
  obtain ⟨hb,hf,hl,hr⟩ := simEnterBinder_fields e
  rw [hb,hf,hl,hr] at h
  rw [fixedFormulaTranslation_all p _ _ _ _ hp]
  exact universalVacuity x (simBase e) _ h

theorem generalVacuity_ex (x e p : M) (hp : IsUFormula SourceL p)
    (h : GeneralVacuity x (simEnterBinder e) p) : GeneralVacuity x e (^∃ p) := by
  unfold GeneralVacuity at h ⊢
  obtain ⟨hb,hf,hl,hr⟩ := simEnterBinder_fields e
  rw [hb,hf,hl,hr] at h
  rw [fixedFormulaTranslation_ex p _ _ _ _ hp]
  unfold exValue
  exact negationVacuity x _ (universalVacuity x (simBase e) _ (negationVacuity x _ h))

/-- Atomic translation is independent of the next binder-label counter. -/
theorem positiveAtom_base_irrelevant (r v bound free base₁ base₂ reserve : M)
    (hr : SourceL.IsRel 2 r) (hv : IsUTermVec SourceL 2 v) :
    F fixedFormulaTranslation ![^rel (2 : M) r v,bound,free,base₁,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r v,bound,free,base₂,reserve] := by
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]

theorem generalVacuity_positiveAtom (x e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hxa : x ≠ F termLabelCode ![a,simBound e,simFree e])
    (hxb : x ≠ F termLabelCode ![b,simBound e,simFree e]) (hxz : x ≠ simReserve e) :
    GeneralVacuity x e (^rel (2 : M) r ?[a,b]) := by
  let e' := pair (simBound e) (pair (simFree e) (pair x (simReserve e)))
  have he : simBound e' = simBound e ∧ simFree e' = simFree e ∧ simBase e' = x ∧ simReserve e' = simReserve e := by
    simp [e',simBound,simFree,simBase,simReserve]
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := he
  have h := positiveAtomVacuity e' r a b hr ha hb
    (by simpa only [hbound,hfree,hbase] using hxa)
    (by simpa only [hbound,hfree,hbase] using hxb)
    (by simpa only [hbase,hreserve] using hxz)
  dsimp only at h
  rw [hbound,hfree,hbase,hreserve] at h
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  rw [positiveAtom_base_irrelevant r _ _ _ x (simBase e) _ hr hv] at h
  exact h

theorem generalVacuity_negativeAtom (x e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hxa : x ≠ F termLabelCode ![a,simBound e,simFree e])
    (hxb : x ≠ F termLabelCode ![b,simBound e,simFree e]) (hxz : x ≠ simReserve e) :
    GeneralVacuity x e (^nrel (2 : M) r ?[a,b]) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have h := generalVacuity_positiveAtom x e r a b hr ha hb hxa hxb hxz
  unfold GeneralVacuity at h ⊢
  rw [fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact negationVacuity x _ h

#print axioms positiveAtom_base_irrelevant
#print axioms generalVacuity_positiveAtom
#print axioms generalVacuity_negativeAtom
#print axioms simEnterBinder_fields
#print axioms generalVacuity_verum
#print axioms generalVacuity_falsum
#print axioms generalVacuity_and
#print axioms generalVacuity_or
#print axioms generalVacuity_all
#print axioms generalVacuity_ex
end models
end PA194ModelLogic
