import PA194CloseTraceLift
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance repeatPushHistoryZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatPushHistoryOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatPushHistoryAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatPushHistoryMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatPushHistoryLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatPushHistoryIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fixed arithmetic graph for entering one source eigenvariable. -/
noncomputable def pushStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. ∃ b, !pi₁Def b previous ∧ ∃ t, !pi₂Def t previous ∧
    ∃ f, !pi₁Def f t ∧ ∃ u, !pi₂Def u t ∧
    ∃ a, !pi₁Def a u ∧ ∃ r, !pi₂Def r u ∧
    ∃ q, !(LO.FirstOrder.Arithmetic.pairDef) q a f ∧
    ∃ x, !(LO.FirstOrder.Arithmetic.pairDef) x (a+1) r ∧
    ∃ y, !(LO.FirstOrder.Arithmetic.pairDef) y (q+1) x ∧
    !(LO.FirstOrder.Arithmetic.pairDef) out b y”
noncomputable def pushIterBlueprint : PR.Blueprint 1 where
  zero := sourceQVecZeroDef
  succ := pushStepDef
noncomputable def pushIterConstruction : PR.Construction M pushIterBlueprint where
  zero p := p 0
  succ _ _ previous := simPushFree previous
  zero_defined := .mk fun e => by simp [pushIterBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by
    simp [pushIterBlueprint,pushStepDef,simPushFree,simBound,simFree,simBase,simReserve, pi₁,pi₂]

theorem pushIter_exists_trace (seed limit : M) :
    ∃ s : M, (pushIterConstruction (M := M)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem pushIter_trace_start (seed s : M) (h : (pushIterConstruction (M := M)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : M), seed⟫ ∈ s := by simpa [pushIterConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem pushIter_trace_step (seed limit s i : M)
    (h : (pushIterConstruction (M := M)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = simPushFree (znth s i) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, simPushFree (znth s i)⟫ ∈ s := by simpa [pushIterConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

/-- Canonical model-valued iterations of closure and environment push. -/
noncomputable def modelClose (n p : M) : M := (closeIterConstruction (M := M)).result ![p] n
noncomputable def modelPush (n e : M) : M := (pushIterConstruction (M := M)).result ![e] n

theorem modelClose_scope (n p : M) (hp : IsSemiformula SourceL 0 p) :
    IsSemiformula SourceL 0 (modelClose n p) := by
  obtain ⟨s,hs,hl,hm⟩ := (closeIterConstruction (M := M)).result_spec ![p] n
  have heq := hs.seq.znth_eq_of_mem hm
  unfold modelClose
  rw [←heq]
  exact closeIter_trace_scoped p n s n hs hl hp (le_refl n)

theorem modelClose_leaf (n e p : M) (hp : IsSemiformula SourceL 0 p)
    (ht : numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (modelPush n e) p) 1)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (modelClose n p)) 1) := by
  obtain ⟨fs,hfs,hfl,hfm⟩ := (closeIterConstruction (M := M)).result_spec ![p] n
  obtain ⟨es,hes,hel,hem⟩ := (pushIterConstruction (M := M)).result_spec ![e] n
  have hclose := hfs.seq.znth_eq_of_mem hfm
  have hpush := hes.seq.znth_eq_of_mem hem
  have hstart := pushIter_trace_start e es hes
  have hstep : ∀ j < n, znth es (j+1) = simPushFree (znth es j) := by
    intro j hj
    exact pushIter_trace_step e n es j hes hel hj
  have ht' : numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr (znth es n) p) 1) := by
    simpa only [hpush,modelPush] using ht
  have hout := closeTrace_leaf p n fs es hfs hfl hp hstep ht'
  simpa only [hstart,hclose,modelClose] using hout

#print axioms modelClose_scope
#print axioms modelClose_leaf
#print axioms pushIter_exists_trace
#print axioms pushIter_trace_start
#print axioms pushIter_trace_step
end models
end PA194BindSource
