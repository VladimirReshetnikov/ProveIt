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
namespace PA194IsoZeroAt
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

def zeroIsoBound2 : Semiproposition M6.PA.RelationalSource.language 2 :=
  Ordinal.zero (.bvar 1) 🡒 orderIso (.bvar 1) (.bvar 0) 🡒 Ordinal.zero (.bvar 0)
def zeroIsoLeft2 : Semiproposition M6.PA.RelationalSource.language 2 := Ordinal.zero (.bvar 1)
def zeroIsoRight2 : Semiproposition M6.PA.RelationalSource.language 2 := Ordinal.zero (.bvar 0)
def zeroIsoIso2 : Semiproposition M6.PA.RelationalSource.language 2 := orderIso (.bvar 1) (.bvar 0)
def zeroIsoDomain2 : Semiproposition M6.PA.RelationalSource.language 2 := Ordinal.domain (.bvar 0)

theorem isoZeroGuard (a b : M) :
    ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      ((⌜zeroIsoDomain2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) ⋏
      ((⌜zeroIsoIso2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) := by
  have he : (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2) = (⌜zeroIsoDomain2⌝ : Semiformula M SourceL 2) ⋏ (⌜zeroIsoIso2⌝ : Semiformula M SourceL 2) := by
    simp [isoGuardTemplate,zeroIsoDomain2,zeroIsoIso2]
  rw [he]
  simp

theorem zeroIsoLeftAt (a b : M) :
    ((⌜zeroIsoLeft2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a] := by
  have hs : zeroIsoLeft2 = zeroTemplate ⇜ ![#1] := by
    simp only [zeroIsoLeft2,zeroTemplate]
    ordinalSyntax
  have ht : (⌜zeroIsoLeft2⌝ : Semiformula M SourceL 2) = (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 1] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem zeroIsoRightAt (a b : M) :
    ((⌜zeroIsoRight2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b] := by
  have hs : zeroIsoRight2 = zeroTemplate ⇜ ![#0] := by
    simp only [zeroIsoRight2,zeroTemplate]
    ordinalSyntax
  have ht : (⌜zeroIsoRight2⌝ : Semiformula M SourceL 2) = (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 0] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem zeroIsoDomainAt (a b : M) :
    ((⌜zeroIsoDomain2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      (⌜domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b] := by
  have hs : zeroIsoDomain2 = domainTemplate ⇜ ![#0] := by
    simp only [zeroIsoDomain2,domainTemplate]
    ordinalSyntax
  have ht : (⌜zeroIsoDomain2⌝ : Semiformula M SourceL 2) = (⌜domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 0] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

noncomputable def isoZeroAtCode (c a b ctx du dz dg hb : M) : M :=
  let vec := (?[ ^&b, ^&a] : M)
  let left := subst SourceL vec (⌜zeroIsoLeft2⌝ : M)
  let right := subst SourceL vec (⌜zeroIsoRight2⌝ : M)
  let iso := subst SourceL vec (⌜zeroIsoIso2⌝ : M)
  let dom := subst SourceL vec (⌜zeroIsoDomain2⌝ : M)
  let di := contextAndRightCode dom iso ctx dg
  let dd := contextAndLeftCode dom iso ctx dg
  let sp := contextDoubleCode (⌜zeroIsoBound2⌝ : M) (^&b) (^&a) ctx du
  let imp := neg SourceL iso ^⋎ right
  let z1 := contextMPCode left imp ctx sp dz
  let z2 := contextMPCode iso right ctx z1 di
  ordinalBaseAtCode c b ctx hb dd z2

noncomputable def isoZeroAtGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out c a b ctx du dz dg hb.
    ∃ bt, !(fixedFormulaQuoteGraph zeroIsoBound2) bt ∧ ∃ lt, !(fixedFormulaQuoteGraph zeroIsoLeft2) lt ∧
    ∃ rt, !(fixedFormulaQuoteGraph zeroIsoRight2) rt ∧ ∃ it, !(fixedFormulaQuoteGraph zeroIsoIso2) it ∧
    ∃ dt, !(fixedFormulaQuoteGraph zeroIsoDomain2) dt ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧
    ∃ v1, !adjoinDef v1 va 0 ∧ ∃ vec, !adjoinDef vec vb v1 ∧
    ∃ left, !(substsGraph SourceL) left vec lt ∧ ∃ right, !(substsGraph SourceL) right vec rt ∧
    ∃ iso, !(substsGraph SourceL) iso vec it ∧ ∃ dom, !(substsGraph SourceL) dom vec dt ∧
    ∃ di, !contextAndRightGraph di dom iso ctx dg ∧ ∃ dd, !contextAndLeftGraph dd dom iso ctx dg ∧
    ∃ sp, !contextDoubleGraph sp bt vb va ctx du ∧ ∃ ni, !(negGraph SourceL) ni iso ∧ ∃ imp, !qqOrDef imp ni right ∧
    ∃ z1, !contextMPGraph z1 left imp ctx sp dz ∧ ∃ z2, !contextMPGraph z2 iso right ctx z1 di ∧
    !ordinalBaseAtGraph out c b ctx hb dd z2”

theorem isoZeroAtGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → M => isoZeroAtCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) isoZeroAtGraph := by
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  haveI := ordinalBaseAtGraph_defined (M := M)
  exact .mk fun w => by simp [isoZeroAtGraph,isoZeroAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoZeroAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜zeroIsoStatement⌝ : Formula M SourceL) Γ)
    (dz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let body : Semiformula M SourceL 2 := ⌜zeroIsoBound2⌝
  let left : Semiformula M SourceL 2 := ⌜zeroIsoLeft2⌝
  let right : Semiformula M SourceL 2 := ⌜zeroIsoRight2⌝
  let iso : Semiformula M SourceL 2 := ⌜zeroIsoIso2⌝
  let dom : Semiformula M SourceL 2 := ⌜zeroIsoDomain2⌝
  let L : Formula M SourceL := left.subst ![Semiterm.fvar b,Semiterm.fvar a]
  let R : Formula M SourceL := right.subst ![Semiterm.fvar b,Semiterm.fvar a]
  let I : Formula M SourceL := iso.subst ![Semiterm.fvar b,Semiterm.fvar a]
  let D : Formula M SourceL := dom.subst ![Semiterm.fvar b,Semiterm.fvar a]
  have he : body = left 🡒 (iso 🡒 right) := by
    simp [body,left,iso,right,zeroIsoBound2,zeroIsoLeft2,zeroIsoIso2,zeroIsoRight2,Semiformula.imp_def]
  have hu : (⌜zeroIsoStatement⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by simp [zeroIsoStatement,body,zeroIsoBound2]
  let du' := TDerivation.cast (congrArg (fun z => insert z Γ) hu) du
  let sp := contextDoubleProof T Γ body (Semiterm.fvar b) (Semiterm.fvar a) du'
  have hi : (body.subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) = L 🡒 (I 🡒 R) := by
    rw [he]; simp [L,I,R]
  let sp' := TDerivation.cast (congrArg (fun z => insert z Γ) hi) sp
  let dg' := TDerivation.cast (congrArg (fun z => insert z Γ) (isoZeroGuard a b)) dg
  let di := contextAndRightProof T Γ D I dg'
  let dd := contextAndLeftProof T Γ D I dg'
  let dz' := TDerivation.cast (congrArg (fun z => insert z Γ) (zeroIsoLeftAt a b).symm) dz
  let z1 := contextMPProof T Γ L (I 🡒 R) sp' dz'
  let z2 := contextMPProof T Γ I R z1 di
  let dd' := TDerivation.cast (congrArg (fun z => insert z Γ) (zeroIsoDomainAt a b)) dd
  let z2' := TDerivation.cast (congrArg (fun z => insert z Γ) (zeroIsoRightAt a b)) z2
  exact ordinalBaseAtProof T Γ c b hc hb dd' z2'

@[simp] theorem isoZeroAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜zeroIsoStatement⌝ : Formula M SourceL) Γ)
    (dz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    (isoZeroAtProof T Γ c a b hc du dz dg hb).val = isoZeroAtCode c a b Γ.val du.val dz.val dg.val hb.val := by
  simp [isoZeroAtProof,isoZeroAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoZeroAtGraph_defined
#print axioms isoZeroAtProof
#print axioms isoZeroAtProof_val
#print axioms isoZeroGuard
#print axioms zeroIsoLeftAt
#print axioms zeroIsoRightAt
#print axioms zeroIsoDomainAt
end models
end PA194IsoZeroAt
