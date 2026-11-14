import PA194SourceHead2Logic
import PA194SourceHead2Syntax
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace PA194SourceHead2Preservation
open PA194SourceHead2Logic PA194SourceHead2Syntax
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceHead6Preservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
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


lemma head2_distinct (d a h : M) (hda : d ≠ a) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (allSource d (allSource a h)) (allSource a (allSource d h)))) := by
  have hnz := imp_nonzero_left (allSource d (allSource a h)) (allSource a (allSource d h)) (allSource_nonzero _ _)
  rw [imp_code _ _ hnz, universal_code d (allSource a h), universal_code a (allSource d h),
    universal_code a h, universal_code d h]
  have hp : IsFormula ℒₒᵣ (translated h) := (fixed_all_wf h).1
  have hpa := PA194InternalFormulaClose.close_wellformed a 0 (translated h) hp
  have hpd := PA194InternalFormulaClose.close_wellformed d 0 (translated h) hp
  rw [PA194InternalFormulaClose.close_all d 0 _ hpa.isUFormula,
    PA194InternalFormulaClose.close_all a 0 _ hpd.isUFormula]
  simp only [zero_add]
  have ht : (1 : M)+1 = 2 := by norm_num
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 2 := ⟨PA194InternalFormulaClose.close d 1 (PA194InternalFormulaClose.close a 0 (translated h)), by
    have hz := PA194InternalFormulaClose.close_wellformed d 1 _ (by simpa using hpa)
    rw [ht] at hz
    exact hz⟩
  let S : Bootstrapping.Semiformula M ℒₒᵣ 2 := ⟨PA194InternalFormulaClose.close a 1 (PA194InternalFormulaClose.close d 0 (translated h)), by
    have hz := PA194InternalFormulaClose.close_wellformed a 1 _ (by simpa using hpd)
    rw [ht] at hz
    exact hz⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) (((∀⁰ ∀⁰ Q) 🡒 ∀⁰ ∀⁰ S).val)
  have hswap : Q.subst ![Bootstrapping.Semiterm.bvar 1, Bootstrapping.Semiterm.bvar 0] = S := by
    apply Bootstrapping.Semiformula.ext
    have hz := close_swap_formula d a 0 (translated h) hda hp ?[^#1,^#0] swapVec_zero
    simpa [Q,S,Bootstrapping.Semiformula.val_substs, Bootstrapping.SemitermVec.val, matrixToVec, adjoin_def] using hz
  rw [← hswap]
  exact (tprovable_iff_provable).mp (exchange_forall Q)

lemma head2 (d a h : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (allSource d (allSource a h)) (allSource a (allSource d h)))) := by
  by_cases hda : d=a
  · subst a
    exact identity_code (allSource d (allSource d h))
  · exact head2_distinct d a h hda
#print axioms head2
#print axioms head2_distinct
end models
end PA194SourceHead2Preservation
