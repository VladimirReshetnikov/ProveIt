import PA194SourceUniversalPreservation
import PA194SourceRho8Preservation
/-! Model-uniform PA provability of the numerical universal-distribution
axiom family, including the zero-implication alias. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194SourceHead6Preservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceAllPreservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def all_distrib (P Q : Bootstrapping.Semiformula M ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢! (∀⁰ P) 🡒 (∀⁰ (P 🡒 Q)) 🡒 ∀⁰ Q := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply TProof.generalize
  have hP : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! P.free := by
    have hu : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! ∀⁰ P.shift := by
      simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! (∀⁰ P).shift)
    simpa [Bootstrapping.Semiformula.free] using TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  have hPQ : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! P.free 🡒 Q.free := by
    have hu : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! ∀⁰ (P 🡒 Q).shift := by
      simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ (P 🡒 Q)).shift, (∀⁰ P).shift] ⊢[T]! (∀⁰ (P 🡒 Q)).shift)
    simpa [Bootstrapping.Semiformula.free] using TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  exact hPQ ⨀ hP

noncomputable def allSource (label body : M) : M := 4*cantor body label+2

lemma allSource_nonzero (label body : M) : allSource label body ≠ 0 := by
  have htwo : (0 : M) < 2 := by norm_num
  have hh : (2 : M) ≤ allSource label body := by unfold allSource; exact le_add_self
  exact ne_of_gt (lt_of_lt_of_le htwo hh)

lemma universal_code (label body : M) :
    translated (allSource label body) = ^∀ (PA194InternalFormulaClose.close label 0 (translated body)) :=
  PA194SourceAllPreservation.universal_code label body

lemma close_imp (label φ ψ : M) (hφ : IsFormula ℒₒᵣ φ) (hψ : IsFormula ℒₒᵣ ψ) :
    PA194InternalFormulaClose.close label 0 (imp ℒₒᵣ φ ψ) =
      imp ℒₒᵣ (PA194InternalFormulaClose.close label 0 φ) (PA194InternalFormulaClose.close label 0 ψ) := by
  unfold imp
  rw [PA194InternalFormulaClose.close_or label 0 _ _ hφ.isUFormula.neg hψ.isUFormula,
    PA194CloseNegation.close_neg label 0 φ hφ]

lemma identity_code (x : M) : Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource x x)) := by
  by_cases hx : x = 0
  · subst x
    have hz : impSource (0 : M) 0 = 0 := by simp [impSource,cantor,triangle]
    simpa [hz] using zero_provable (M := M)
  · rw [imp_code x x (imp_nonzero_left x x hx)]
    let P : Bootstrapping.Formula M ℒₒᵣ := ⟨translated x, (fixed_all_wf x).1⟩
    change Provable (𝗣𝗔 : ArithmeticTheory) ((P 🡒 P).val)
    exact (tprovable_iff_provable).mp ⟨C_id⟩

lemma head6_alias (label a h : M) (halias : impSource a h = 0) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (allSource label a)
      (impSource (allSource label (impSource a h)) (allSource label h)))) := by
  obtain ⟨rfl,rfl⟩ := PA194SourceMPPreservation.implication_zero a h halias
  rw [halias]
  exact imp_conseq (allSource label 0) (impSource (allSource label 0) (allSource label 0))
    (identity_code (allSource label 0))

lemma head6_nonzero (label a h : M) (hnz : impSource a h ≠ 0) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (allSource label a)
      (impSource (allSource label (impSource a h)) (allSource label h)))) := by
  have hU1 := allSource_nonzero label a
  have hU2 := allSource_nonzero label (impSource a h)
  have hI : impSource (allSource label (impSource a h)) (allSource label h) ≠ 0 := imp_nonzero_left _ _ hU2
  have hOuter : impSource (allSource label a) (impSource (allSource label (impSource a h)) (allSource label h)) ≠ 0 := imp_nonzero_left _ _ hU1
  rw [imp_code _ _ hOuter, imp_code _ _ hI, universal_code label a,
    universal_code label (impSource a h), universal_code label h, imp_code a h hnz]
  have ha : IsFormula ℒₒᵣ (translated a) := (fixed_all_wf a).1
  have hh : IsFormula ℒₒᵣ (translated h) := (fixed_all_wf h).1
  rw [close_imp label (translated a) (translated h) ha hh]
  let P : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 (translated a), by
    simpa using PA194InternalFormulaClose.close_wellformed label 0 (translated a) ha⟩
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 (translated h), by
    simpa using PA194InternalFormulaClose.close_wellformed label 0 (translated h) hh⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) (((∀⁰ P) 🡒 (∀⁰ (P 🡒 Q)) 🡒 ∀⁰ Q).val)
  exact (tprovable_iff_provable).mp ⟨all_distrib P Q⟩

lemma head6 (label a h : M) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (allSource label a)
      (impSource (allSource label (impSource a h)) (allSource label h)))) := by
  by_cases hzero : impSource a h = 0
  · exact head6_alias label a h hzero
  · exact head6_nonzero label a h hzero

#print axioms head6
#print axioms all_distrib
end models
end PA194SourceHead6Preservation
