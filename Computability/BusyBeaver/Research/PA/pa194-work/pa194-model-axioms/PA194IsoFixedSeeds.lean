import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoWitnessBranch
import PA194OrdinalStepApplicationCode
import PA194IsoWitnessStepComponents
import PA194IsoGuardMatch
import PA194IsoSuccessorProperty
import PA194IsoSuccessorSuppliers
import PA194FixedInstanceShift
import PA194IsoGuardAt
import PA194OrderIsoZeroModel
import PA194IsoZeroAt
import PA194IsoGuardOpen
import PA194IsoGuardZero
import PA194SeedProofDelta
import PA194LeastSeed
import PA194IsoMatchUniversal
import PA194OrdinalBaseApplicationCode
import PA194DomainInstances
import PA194BadTraceStepShift
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoFixedSeeds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IsoMatchTemplate PA194ContextAllCode PA194FixedSyntaxQuote PA194IsoGuardProperty PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource


open PA194ContextAndProjectionCode PA194IsoMatchAtCode M6.PA.RelationalSource.PairGraph

open PA194ContextAndProjectionCode PA194IsoMatchWitness

open PA194InductionStepShiftCode PA194IsoWitnessComponents PA194OrdinalStepQuote PA194InternalOrdinalStep PA194OrdinalStepApplicationCode PA194IsoWitnessBranch

open PA194IsoWitnessStepComponents PA194IsoGuardMatch

open PA194OrdinalStepFromProperty PA194IsoSuccessorProperty PA194DomainInstances PA194OrdinalBaseQuote PA194BadTraceStepShift


open PA194OrderIsoZeroModel PA194OrdinalBaseApplicationCode PA194OrdinalBaseQuote PA194InternalOrdinalBase PA194InductionBaseShiftCode PA194ContextDoubleSpecializeCode M6.PA.RelationalSource.PairGraph

open PA194IsoZeroAt PA194IsoGuardOpen PA194FixedInstanceShift PA194ContextualBaseShift PA194IsoGuardAt

open PA194IsoGuardZero PA194SeedProofDelta PA194LeastSeed PA194OrdinalSeededCode PA194FullSepOpen PA194IsoMatchUniversal PA194IsoMatchTemplate

noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta

/-- Every internal proof of a fixed standard sentence yields a least proof code. -/
theorem fixedSeed_exists (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    ∃ d : M, Proof adjunctiveFullSepTheory d (⌜φ⌝ : M) := by
  refine ⟨h.val, ?_⟩
  simpa [Proof,Tfull,← singleton_eq_insert,← Semiformula.quote_def] using h.derivationOf

theorem leastFixedSeed_exists (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    ∃ d : M, Proof adjunctiveFullSepTheory d (⌜φ⌝ : M) ∧
      ∀ e < d, ¬ Proof adjunctiveFullSepTheory e (⌜φ⌝ : M) := by
  letI := adjunctiveFullSepTheoryDelta
  letI := seedProofDelta_defined (M := M) φ
  obtain ⟨x,hx⟩ := fixedSeed_exists φ h
  exact InductionOnHierarchy.least_number_sigma 𝚺 1 (P := fun d => Proof adjunctiveFullSepTheory d (⌜φ⌝ : M)) (by definability) hx

noncomputable def leastFixedSeed (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) : M := Classical.choose (leastFixedSeed_exists φ h)

theorem leastFixedSeed_spec (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    Proof adjunctiveFullSepTheory (leastFixedSeed φ h) (⌜φ⌝ : M) ∧
      ∀ e < leastFixedSeed φ h, ¬ Proof adjunctiveFullSepTheory e (⌜φ⌝ : M) := Classical.choose_spec (leastFixedSeed_exists φ h)

noncomputable def leastFixedSeedGraph (φ : Proposition M6.PA.RelationalSource.language) : 𝚺₁.Semisentence 2 := .mkSigma
  “out ignored. !(seedProofDelta φ).sigma out ∧ ∀ z < out, ¬!(seedProofDelta φ).pi z”

theorem leastFixedSeedGraph_defined (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    𝚺₁-Function₁ (fun _ : M => leastFixedSeed φ h) via leastFixedSeedGraph φ := by
  letI := adjunctiveFullSepTheoryDelta
  letI := seedProofDelta_defined (M := M) φ
  have unique (x : M) (hx : Proof adjunctiveFullSepTheory x (⌜φ⌝ : M) ∧ ∀ y < x, ¬ Proof adjunctiveFullSepTheory y (⌜φ⌝ : M)) : x = leastFixedSeed φ h := by
    have hy := leastFixedSeed_spec φ h
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      exact hx.2 _ hlt hy.1
    · apply le_of_not_gt
      intro hlt
      exact hy.2 _ hlt hx.1
  refine .mk fun v => ?_
  simp [leastFixedSeedGraph,HierarchySymbol.Semiformula.val_sigma,HierarchySymbol.Defined.iff_delta_sigma,
    HierarchySymbol.Defined.iff_delta_pi]
  constructor
  · exact unique _
  · intro eq
    rw [eq]
    exact leastFixedSeed_spec φ h

noncomputable def fixedSeedProof (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL) := by
  refine ⟨leastFixedSeed φ h, ?_⟩
  have hs := (leastFixedSeed_spec φ h).1
  simpa [Proof,Tfull,← singleton_eq_insert,← Semiformula.quote_def] using hs

@[simp] theorem fixedSeedProof_val (φ : Proposition M6.PA.RelationalSource.language)
    (h : (Tfull (M := M)) ⊢! (⌜φ⌝ : Formula M SourceL)) :
    (fixedSeedProof φ h).val = leastFixedSeed φ h := rfl

noncomputable def zeroIsoSeed : M := leastFixedSeed zeroIsoStatement (zeroIsoClosedProof (Tfull (M := M)))
noncomputable def matchIsoSeed : M := leastFixedSeed (∀⁰ ∀⁰ ∀⁰ isoMatchBound) (isoMatchUniversalProof (M := M))

theorem zeroIsoSeed_defined : 𝚺₁-Function₁ (fun _ : M => zeroIsoSeed (M := M)) via leastFixedSeedGraph zeroIsoStatement :=
  leastFixedSeedGraph_defined zeroIsoStatement (zeroIsoClosedProof (Tfull (M := M)))

theorem matchIsoSeed_defined : 𝚺₁-Function₁ (fun _ : M => matchIsoSeed (M := M)) via leastFixedSeedGraph (∀⁰ ∀⁰ ∀⁰ isoMatchBound) :=
  leastFixedSeedGraph_defined (∀⁰ ∀⁰ ∀⁰ isoMatchBound) (isoMatchUniversalProof (M := M))

noncomputable def zeroIsoSeedProof : (Tfull (M := M)) ⊢! (⌜zeroIsoStatement⌝ : Formula M SourceL) :=
  fixedSeedProof zeroIsoStatement (zeroIsoClosedProof (Tfull (M := M)))
noncomputable def matchIsoSeedProof : (Tfull (M := M)) ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) :=
  fixedSeedProof (∀⁰ ∀⁰ ∀⁰ isoMatchBound) (isoMatchUniversalProof (M := M))

noncomputable def fullZeroCode (c a ctx dz hb : M) : M :=
  let seed := zeroIsoSeed (M := M)
  let du := wkRule (insert (⌜zeroIsoStatement⌝ : M) ctx) seed
  isoGuardZeroCode c a ctx du dz hb

noncomputable def fullZeroGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out c a ctx dz hb. ∃ seed, !(leastFixedSeedGraph zeroIsoStatement) seed 0 ∧
    ∃ u, !(fixedFormulaQuoteGraph zeroIsoStatement) u ∧ ∃ us, !insertDef us u ctx ∧
    ∃ du, !wkRuleGraph du us seed ∧ !isoGuardZeroGraph out c a ctx du dz hb”

theorem fullZeroGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 5 → M => fullZeroCode (w 0) (w 1) (w 2) (w 3) (w 4)) fullZeroGraph := by
  haveI := zeroIsoSeed_defined (M := M)
  haveI := isoGuardZeroGraph_defined (M := M)
  exact .mk fun w => by simp [fullZeroGraph,fullZeroCode,fixedFormulaQuoteGraph_correct]

noncomputable def fullZeroProof (Γ : Sequent M SourceL) (c a : M) (hc : IsSemiformula SourceL 1 c)
    (dz : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hb : (Tfull (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let du : (Tfull (M := M)) ⊢!ᵈᵉʳ insert (⌜zeroIsoStatement⌝ : Formula M SourceL) Γ :=
    TDerivation.wk (zeroIsoSeedProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact isoGuardZeroProof (Tfull (M := M)) Γ c a hc du dz hb

@[simp] theorem fullZeroProof_val (Γ : Sequent M SourceL) (c a : M) (hc : IsSemiformula SourceL 1 c)
    (dz : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hb : (Tfull (M := M)) ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    (fullZeroProof Γ c a hc dz hb).val = fullZeroCode c a Γ.val dz.val hb.val := by
  simp [fullZeroProof,fullZeroCode,zeroIsoSeedProof,zeroIsoSeed,Semiformula.quote_def]

noncomputable def fullSuccessorCode (c a p ctx ds dq hstep : M) : M :=
  let seed := matchIsoSeed (M := M)
  let du := wkRule (insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : M) ctx) seed
  isoGuardSuccessorCode c a p ctx du ds dq hstep

noncomputable def fullSuccessorGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out c a p ctx ds dq hstep. ∃ seed, !(leastFixedSeedGraph (∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)) seed 0 ∧
    ∃ u, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)) u ∧ ∃ us, !insertDef us u ctx ∧
    ∃ du, !wkRuleGraph du us seed ∧ !isoGuardSuccessorGraph out c a p ctx du ds dq hstep”

theorem fullSuccessorGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → M => fullSuccessorCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) fullSuccessorGraph := by
  haveI := matchIsoSeed_defined (M := M)
  haveI := isoGuardSuccessorGraph_defined (M := M)
  exact .mk fun w => by simp [fullSuccessorGraph,fullSuccessorCode,fixedFormulaQuoteGraph_correct]

noncomputable def fullSuccessorProof (Γ : Sequent M SourceL) (c a p : M) (hc : IsSemiformula SourceL 1 c)
    (ds : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar p]) Γ)
    (dq : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : (Tfull (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let u : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : (Tfull (M := M)) ⊢!ᵈᵉʳ insert u Γ :=
    TDerivation.wk (matchIsoSeedProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact isoGuardSuccessorProof (Tfull (M := M)) Γ c a p hc du ds dq hstep

@[simp] theorem fullSuccessorProof_val (Γ : Sequent M SourceL) (c a p : M) (hc : IsSemiformula SourceL 1 c)
    (ds : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar p]) Γ)
    (dq : (Tfull (M := M)) ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : (Tfull (M := M)) ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    (fullSuccessorProof Γ c a p hc ds dq hstep).val = fullSuccessorCode c a p Γ.val ds.val dq.val hstep.val := by
  simp [fullSuccessorProof,fullSuccessorCode,matchIsoSeedProof,matchIsoSeed,Semiformula.quote_def]

#print axioms fullZeroGraph_defined
#print axioms fullZeroProof_val
#print axioms fullSuccessorGraph_defined
#print axioms fullSuccessorProof_val
#print axioms leastFixedSeedGraph_defined
#print axioms fixedSeedProof_val
#print axioms zeroIsoSeed_defined
#print axioms matchIsoSeed_defined
#print axioms zeroIsoSeedProof
#print axioms matchIsoSeedProof
end models
end PA194IsoFixedSeeds
