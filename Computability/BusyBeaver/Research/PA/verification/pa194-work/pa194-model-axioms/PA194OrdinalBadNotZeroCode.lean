import PA194OrdinalBaseApplicationCode
import PA194InternalBaseAtContext
import PA194FixedSyntaxQuote
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalBadNotZeroCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OrdinalBaseApplicationCode PA194BindSource PA194ContextBaseApplicationCode PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194TypedSeparation
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A bad ordinal is nonzero: explicit contextual proof code. -/
noncomputable def badNotZeroCode (p a g hb hd hn : M) : M :=
  let dt := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let zt := (⌜zeroTemplate⌝ : M)
  let t := ^&a
  let dom := substs1 SourceL t dt
  let zero := substs1 SourceL t zt
  let prop := substs1 SourceL t p
  let target := insert (neg SourceL zero) g
  let dz := axL (insert zero target) zero
  let wb := wkRule (insert (baseCode p) target) hb
  let wd := wkRule (insert dom target) hd
  let wn := wkRule (insert (neg SourceL prop) target) hn
  let pos := ordinalBaseAtCode p a target wb wd dz
  cutRule target prop pos wn

noncomputable def badNotZeroGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p a g hb hd hn. ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧
    ∃ zt, !(fixedFormulaQuoteGraph zeroTemplate) zt ∧ ∃ t, !qqFvarDef t a ∧
    ∃ dom, !(substs1Graph SourceL) dom t dt ∧ ∃ zero, !(substs1Graph SourceL) zero t zt ∧
    ∃ prop, !(substs1Graph SourceL) prop t p ∧ ∃ nz, !(negGraph SourceL) nz zero ∧
    ∃ target, !insertDef target nz g ∧ ∃ zs, !insertDef zs zero target ∧ ∃ dz, !axLGraph dz zs zero ∧
    ∃ base, !inductionBaseGraph base dt zt p ∧ ∃ bs, !insertDef bs base target ∧ ∃ wb, !wkRuleGraph wb bs hb ∧
    ∃ doms, !insertDef doms dom target ∧ ∃ wd, !wkRuleGraph wd doms hd ∧
    ∃ np, !(negGraph SourceL) np prop ∧ ∃ ns, !insertDef ns np target ∧ ∃ wn, !wkRuleGraph wn ns hn ∧
    ∃ pos, !ordinalBaseAtGraph pos p a target wb wd dz ∧ !cutRuleGraph out target prop pos wn”

theorem badNotZeroGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => badNotZeroCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) badNotZeroGraph := by
  haveI := inductionBaseGraph_defined (M := M)
  haveI := ordinalBaseAtGraph_defined (M := M)
  exact .mk fun v => by simp [badNotZeroGraph,badNotZeroCode,baseCode,fixedFormulaQuoteGraph_correct]

noncomputable def badNotZeroProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ) :
    T ⊢!ᵈᵉʳ insert (∼((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ := by
  let base : Formula M SourceL := ⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩
  let dom : Formula M SourceL := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]
  let zero : Formula M SourceL := (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]
  let prop : Formula M SourceL := (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]
  let target := insert (∼zero) Γ
  let dz : T ⊢!ᵈᵉʳ insert zero target := TDerivation.em zero (by simp) (by simp [target])
  let wb : T ⊢!ᵈᵉʳ insert base target := TDerivation.wk hb (by intro x hx; simp [target] at hx ⊢; tauto)
  let wd : T ⊢!ᵈᵉʳ insert dom target := TDerivation.wk hd (by intro x hx; simp [target] at hx ⊢; tauto)
  let wn : T ⊢!ᵈᵉʳ insert (∼prop) target := TDerivation.wk hn (by intro x hx; simp [target] at hx ⊢; tauto)
  let pos := ordinalBaseAtProof T target p a hp wb wd dz
  exact TDerivation.cut pos wn

@[simp] theorem badNotZeroProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ) :
    (badNotZeroProof T Γ p a hp hb hd hn).val = badNotZeroCode p a Γ.val hb.val hd.val hn.val := by
  simp [badNotZeroProof,badNotZeroCode,Semiformula.quote_def,substs1,SemitermVec.val_succ]

#print axioms badNotZeroGraph_defined
#print axioms badNotZeroProof
#print axioms badNotZeroProof_val
end models
end PA194OrdinalBadNotZeroCode
