import PA194InternalFormulaClose
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions
/-! Internal formula closing commutes with Foundation syntactic negation,
including on nonstandard formulas. This is a syntactic theorem. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194CloseNegation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194InternalFormulaClose
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

theorem close_neg (label depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    close label depth (Bootstrapping.neg ℒₒᵣ p) = Bootstrapping.neg ℒₒᵣ (close label depth p) := by
  haveI : 𝚺₁-Function₂ ((construction (M := M)).result ℒₒᵣ) := (graph (M := M)).to_definable
  have hdef : 𝚺₁-Relation (fun n p : M => close label n (Bootstrapping.neg ℒₒᵣ p) = Bootstrapping.neg ℒₒᵣ (close label n p)) := by
    unfold close
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv
    have hvec := (close_vec_wellformed label n k v hv).isUTerm
    simp [neg_rel hr hv.isUTerm, close_rel label n k r v hr hv.isUTerm,
      close_nrel label n k r v hr hv.isUTerm, hr, hvec]
  · intro n k r v hr hv
    have hvec := (close_vec_wellformed label n k v hv).isUTerm
    simp [neg_nrel hr hv.isUTerm, close_rel label n k r v hr hv.isUTerm,
      close_nrel label n k r v hr hv.isUTerm, hr, hvec]
  · intro n; simp [close_verum,close_falsum]
  · intro n; simp [close_verum,close_falsum]
  · intro n p q hp hq ihp ihq
    have hp' := close_wellformed label n p hp
    have hq' := close_wellformed label n q hq
    simp [neg_and hp.isUFormula hq.isUFormula,close_and label n p q hp.isUFormula hq.isUFormula,
      close_or label n _ _ hp.isUFormula.neg hq.isUFormula.neg, hp'.isUFormula,hq'.isUFormula,ihp,ihq]
  · intro n p q hp hq ihp ihq
    have hp' := close_wellformed label n p hp
    have hq' := close_wellformed label n q hq
    simp [neg_or hp.isUFormula hq.isUFormula,close_or label n p q hp.isUFormula hq.isUFormula,
      close_and label n _ _ hp.isUFormula.neg hq.isUFormula.neg, hp'.isUFormula,hq'.isUFormula,ihp,ihq]
  · intro n p hp ih
    have hp' := close_wellformed label (n+1) p hp
    simp [neg_all hp.isUFormula,close_all label n p hp.isUFormula,
      close_exs label n _ hp.isUFormula.neg,hp'.isUFormula,ih]
  · intro n p hp ih
    have hp' := close_wellformed label (n+1) p hp
    simp [neg_ex hp.isUFormula,close_exs label n p hp.isUFormula,
      close_all label n _ hp.isUFormula.neg,hp'.isUFormula,ih]

#print axioms close_neg
end models
end PA194CloseNegation
