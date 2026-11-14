import PA194AtomShiftCodeModel
import PA194FormulaUpdate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194SourceShiftHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
  PA194StackCode PA194StackHistory PA194ParamHistory PA194NumeralCode PA194TagCode
  PA194TermRecursion PA194CloseFunction PA194VariableDispatch PA194CloseVariable PA194BranchSeed
open PA194FormulaUpdate PA194AtomShiftCodeModel PA194TermShiftCodeModel

def unaryResultSame (first second : Code 1) : Code 4 :=
  tag2 (tag first) (childAt first second (payload first second) (budget second))

noncomputable def shiftNext (first second : Code 1) : Code 4 :=
  let t := tag first
  let is (n : Nat) := bin equalityCode t (numeralCode 4 n)
  let atom := apply4 atomShiftCode (src first)
  selectAmong (is 0) atom
    (selectAmong (is 1) atom
      (selectAmong (is 2) (src first)
        (selectAmong (is 3) (src first)
          (selectAmong (is 4) (binaryResult first second)
            (selectAmong (is 5) (binaryResult first second) (unaryResultSame first second))))))

noncomputable def shiftHistory (first second : Code 1) : Code 4 :=
  PA194FormulaBudget.packedResult (shiftNext first second)

noncomputable def fixedFormulaShiftCode : Code 1 :=
  .comp (shiftHistory firstProjection secondProjection)
    (.cons (.proj 0) (.cons (.zero 1) (.cons (.zero 1) (.cons (.zero 1) (.nil 1)))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelNext (first second : Code 1) (e : Fin 4 → M) :
    F (shiftNext first second) e =
      if F (tag first) e = 0 then F (apply4 atomShiftCode (src first)) e
      else if F (tag first) e = 1 then F (apply4 atomShiftCode (src first)) e
      else if F (tag first) e = 2 then F (src first) e
      else if F (tag first) e = 3 then F (src first) e
      else if F (tag first) e = 4 then F (binaryResult first second) e
      else if F (tag first) e = 5 then F (binaryResult first second) e
      else F (unaryResultSame first second) e := by
  simp only [shiftNext, modelChooseEqual, modelNumeralCode]
  norm_num

theorem modelAtom (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (t r v b label ceiling : M) (ht : t = 0 ∨ t = 1)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F (shiftHistory first second) ![pair t (pair 2 (pair r v))+1,b,label,ceiling] =
      pair t (pair 2 (pair r (termShiftVec M6.PA.RelationalSource.language 2 v)))+1 := by
  rw [shiftHistory, PA194FormulaBudget.modelPackedResult, PA194ParamHistory.modelTranslation,
    modelNext, modelTag first hf]
  have hbranch (yes no : M) : (if t = 0 then yes else if t = 1 then yes else no) = yes := by
    rcases ht with rfl | rfl <;> norm_num
  rw [hbranch, modelApply4, modelSrc first hf]
  have he : (fun _ : Fin 1 => pair t (pair 2 (pair r v))+1) = ![pair t (pair 2 (pair r v))+1] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [he]
  exact atom_model t r v hv

theorem modelTruth (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (t payload b label ceiling : M) (ht : t = 2 ∨ t = 3) :
    F (shiftHistory first second) ![pair t payload+1,b,label,ceiling] = pair t payload+1 := by
  rw [shiftHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf,modelSrc first hf]
  rcases ht with rfl | rfl <;> norm_num

theorem modelBoolean (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p q b label ceiling : M) (ht : t = 4 ∨ t = 5) :
    F (shiftHistory first second) ![pair t (pair p q)+1,b,label,ceiling] =
      pair t (pair (F (shiftHistory first second) ![p,b,label,ceiling])
        (F (shiftHistory first second) ![q,b,label,ceiling])) + 1 := by
  rw [shiftHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf]
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have ht1 : t ≠ 1 := by rcases ht with rfl | rfl <;> norm_num
  have ht2 : t ≠ 2 := by rcases ht with rfl | rfl <;> norm_num
  have ht3 : t ≠ 3 := by rcases ht with rfl | rfl <;> norm_num
  simp only [ht0,ht1,ht2,ht3,if_false]
  have hbranch (y z : M) : (if t = 4 then y else if t = 5 then y else z) = y := by
    rcases ht with rfl | rfl <;> norm_num
  rw [hbranch,modelBinaryResult first second hf hs]
  have hp : p < pair t (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right t (pair p q))) (lt_add_one _)
  have hq : q < pair t (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right t (pair p q))) (lt_add_one _)
  rw [PA194FormulaBudget.lookup_same (shiftNext first second) first second hf hs p (pair t (pair p q)+1) b label ceiling hp,
    PA194FormulaBudget.lookup_same (shiftNext first second) first second hf hs q (pair t (pair p q)+1) b label ceiling hq]

theorem modelUnaryResultSame (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p b hist label ceiling : M) :
    F (unaryResultSame first second) ![pair (pair t p+1) b,hist,label,ceiling] =
      pair t (F (lookupCode (stackComponent first) (stackComponent second))
        ![F distanceCode ![pair (pair t p+1) b,pair p b],hist]) + 1 := by
  rw [unaryResultSame,tag2,modelBin,modelTagValue,modelTag first hf,modelChildAt,
    modelPayload first second hf hs,modelBudget second hs]
  rfl

theorem modelQuantifier (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p b label ceiling : M) (ht : t = 6 ∨ t = 7) :
    F (shiftHistory first second) ![pair t p+1,b,label,ceiling] =
      pair t (F (shiftHistory first second) ![p,b,label,ceiling]) + 1 := by
  rw [shiftHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf]
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have ht1 : t ≠ 1 := by rcases ht with rfl | rfl <;> norm_num
  have ht2 : t ≠ 2 := by rcases ht with rfl | rfl <;> norm_num
  have ht3 : t ≠ 3 := by rcases ht with rfl | rfl <;> norm_num
  have ht4 : t ≠ 4 := by rcases ht with rfl | rfl <;> norm_num
  have ht5 : t ≠ 5 := by rcases ht with rfl | rfl <;> norm_num
  simp only [ht0,ht1,ht2,ht3,ht4,ht5,if_false]
  rw [modelUnaryResultSame first second hf hs]
  rw [PA194FormulaBudget.lookup_same (shiftNext first second) first second hf hs p (pair t p+1) b label ceiling]
  exact lt_of_le_of_lt (le_pair_right t p) (lt_add_one _)

theorem historyDefinable (first second : Code 1) (b label ceiling : M) :
    𝚺₁-Function₁ (fun p : M => F (shiftHistory first second) ![p,b,label,ceiling]) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 4 → M => F (shiftHistory first second) v) :=
    HierarchySymbol.Defined.to_definable (PA194CodeGraph.graph (shiftHistory first second))
      (PA194CodeGraph.modelGraph (shiftHistory first second))
  have hi : ∀ j : Fin 4, 𝚺₁.DefinableFunction (fun v : Fin 1 → M => ![v 0,b,label,ceiling] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.const b
      · refine Fin.cases ?_ (fun m => ?_) l
        · exact HierarchySymbol.DefinableFunction.const label
        · exact Fin.cases (HierarchySymbol.DefinableFunction.const ceiling) (fun n => Fin.elim0 n) m
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  simpa using h

theorem history_correct (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (b label ceiling p : M) (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F (shiftHistory first second) ![p,b,label,ceiling] = shift M6.PA.RelationalSource.language p := by
  letI : 𝚺₁-Function₁ (fun p : M => F (shiftHistory first second) ![p,b,label,ceiling]) :=
    historyDefinable first second b label ceiling
  have hdef : 𝚺₁-Predicate (fun p : M => F (shiftHistory first second) ![p,b,label,ceiling] =
      shift M6.PA.RelationalSource.language p) := by
    definability
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv
    have hk := sourceRelation_arity hr
    subst k
    rw [shift_rel hr hv]
    simpa [qqRel] using modelAtom first second hf 0 r v b label ceiling (Or.inl rfl) hv
  · intro k r v hr hv
    have hk := sourceRelation_arity hr
    subst k
    rw [shift_nrel hr hv]
    simpa [qqNRel] using modelAtom first second hf 1 r v b label ceiling (Or.inr rfl) hv
  · rw [shift_verum]
    simpa [qqVerum] using modelTruth first second hf 2 0 b label ceiling (Or.inl rfl)
  · rw [shift_falsum]
    simpa [qqFalsum] using modelTruth first second hf 3 0 b label ceiling (Or.inr rfl)
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq]
    simpa [qqAnd, ihp, ihq] using modelBoolean first second hf hs 4 p q b label ceiling (Or.inl rfl)
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq]
    simpa [qqOr, ihp, ihq] using modelBoolean first second hf hs 5 p q b label ceiling (Or.inr rfl)
  · intro p hp ih
    rw [shift_all hp]
    simpa [qqAll, ih] using modelQuantifier first second hf hs 6 p b label ceiling (Or.inl rfl)
  · intro p hp ih
    rw [shift_exs hp]
    simpa [qqExs, ih] using modelQuantifier first second hf hs 7 p b label ceiling (Or.inr rfl)

theorem modelFixedRoot (p : M) :
    F fixedFormulaShiftCode ![p] = F (shiftHistory firstProjection secondProjection) ![p,0,0,0] := by
  rw [fixedFormulaShiftCode, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact PRAMultiplication.modelZero _
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact PRAMultiplication.modelZero _
      · exact Fin.cases (PRAMultiplication.modelZero _) (fun m => Fin.elim0 m) l

theorem fixedFormulaShiftCode_correct {p : M} (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F fixedFormulaShiftCode ![p] = shift M6.PA.RelationalSource.language p := by
  rw [modelFixedRoot]
  exact history_correct firstProjection secondProjection firstProjection_certified secondProjection_certified 0 0 0 p hp

theorem fixedFormulaShiftGraph_correct {p y : M}
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    (PA194CodeGraph.graph fixedFormulaShiftCode).val.Eval ![y,p] Empty.elim ↔
      y = shift M6.PA.RelationalSource.language p := by
  have h := (PA194CodeGraph.modelGraph (M := M) fixedFormulaShiftCode).defined ![y,p]
  have he : (fun i : Fin 1 => ![y,p] i.succ) = ![p] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [Matrix.cons_val_zero] at h
  rw [he, fixedFormulaShiftCode_correct hp] at h
  exact h

#print axioms fixedFormulaShiftGraph_correct
#print axioms fixedFormulaShiftCode_correct
#print axioms historyDefinable
#print axioms history_correct
#print axioms modelAtom
#print axioms modelTruth
#print axioms modelBoolean
#print axioms modelQuantifier
#print axioms modelNext
end models
end PA194SourceShiftHistory
