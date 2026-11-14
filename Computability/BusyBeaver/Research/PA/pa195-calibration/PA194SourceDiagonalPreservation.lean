import PA194SourceFreshClose
import PA194SourceHead1Syntax
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceDiagonalPreservation
open PA194SourceFreshClose PA194SourceHead5Preservation PA194SourceHead1Syntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
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



lemma components_lt_pos_tag (a b k : M) (hk : 0 < k) : a < 4*cantor a b+k ∧ b < 4*cantor a b+k := by
  have ht : cantor a b ≤ 4*cantor a b := by
    have hh := Arithmetic.mul_le_mul_right (a := cantor a b) (show (1 : M) ≤ 4 by norm_num)
    simpa [mul_comm] using hh
  have hp : 4*cantor a b < 4*cantor a b+k := lt_add_of_pos_right _ hk
  exact ⟨lt_of_le_of_lt (le_trans (components_le a b).1 ht) hp,
    lt_of_le_of_lt (le_trans (components_le a b).2 ht) hp⟩

lemma source_bounded_fresh (label n : M) (hn : n ≤ label) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated n) = translated n := by
  haveI := formula_definable replaceGraph replaceMap replaceGraph_correct (pair label (label+1))
  have hT : 𝚺₁-Function₁ (fun n : M => F fixedTranslation (fun _ => n)) := by
    have hg : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F fixedTranslation e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) fixedTranslation)
    convert hg using 1
    funext e
    apply congrArg (fun v : Fin 1 → M => F fixedTranslation v)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  haveI := hT
  have hdef : 𝚺₁-Predicate (fun n : M => n ≤ label → renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated n) = translated n) := by
    unfold translated
    definability
  revert hn
  refine ISigma1.sigma1_order_induction hdef ?_ n
  intro x ih hx
  obtain ⟨a,b,h | h | h | h⟩ := source_cases x
  · rw [h] at ih hx ⊢
    by_cases hz : 4*cantor a b = 0
    · rw [hz, translated_zero,rename_verum]
    · have ha := (components_lt_imp a b hz).1
      have hb := (components_lt_imp a b hz).2
      have hp : IsFormula ℒₒᵣ (translated a) := (fixed_all_wf a).1
      have hq : IsFormula ℒₒᵣ (translated b) := (fixed_all_wf b).1
      have hnz : impSource a b ≠ 0 := hz
      change renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated (impSource a b)) = _
      rw [imp_code a b hnz, rename_imp label (label+1) _ _ hp hq, ih a ha (le_trans (le_of_lt ha) hx), ih b hb (le_trans (le_of_lt hb) hx)]
      exact (imp_code a b hnz).symm
  · rw [h] at hx ⊢
    have hs := components_lt_pos_tag a b 1 (by norm_num)
    have ha : a < label := lt_of_lt_of_le hs.1 hx
    have hb : b < label := lt_of_lt_of_le hs.2 hx
    change renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated (memSource a b)) = _
    rw [membership_code, rename_bit]
    simpa [memSource, ne_of_gt ha, ne_of_gt hb] using (membership_code a b).symm
  · rw [h] at ih hx ⊢
    have hs := first_lt_universal a b
    have hp : IsFormula ℒₒᵣ (translated a) := (fixed_all_wf a).1
    have hf := ih a hs (le_trans (le_of_lt hs) hx)
    change renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated (allSource b a)) = _
    rw [universal_code, rename_all replaceGraph replaceMap replaceGraph_correct _ _ (PA194InternalFormulaClose.close_wellformed b 0 (translated a) hp).isUFormula,
      formula_close_keeps_fixed label (label+1) b 0 (translated a) (ne_of_lt (lt_add_one label)) hp hf]
    exact (universal_code b a).symm
  · rw [h] at hx ⊢
    have hs := components_lt_pos_tag a b 3 (by norm_num)
    have ha : a < label := lt_of_lt_of_le hs.1 hx
    have hb : b < label := lt_of_lt_of_le hs.2 hx
    change renameFormula replaceGraph replaceMap replaceGraph_correct (pair label (label+1)) (translated (eqSource a b)) = _
    rw [equality_code, rename_eq]
    simpa [eqSource, ne_of_gt ha, ne_of_gt hb] using (equality_code a b).symm

lemma diagonal (c : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource c (allSource c c))) := by
  have hnz := imp_nonzero_right c (allSource c c) (allSource_nonzero c c)
  rw [imp_code c (allSource c c) hnz, universal_code c c]
  let P : Bootstrapping.Formula M ℒₒᵣ := ⟨translated c,(fixed_all_wf c).1⟩
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close c 0 P.val, by
    simpa using PA194InternalFormulaClose.close_wellformed c 0 P.val P.isSemiformula⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) ((P 🡒 ∀⁰ Q).val)
  have hclose : Q.val = P.val :=
    formula_close_of_fixed c (c+1) 0 P.val (ne_of_lt (lt_add_one c)) P.isSemiformula (source_bounded_fresh c c (le_refl c))
  have hfree : Q.free = P.shift := unbound_free P Q hclose
  apply (tprovable_iff_provable).mp
  apply Nonempty.intro
  apply TProof.generalizeAux
  rw [hfree]
  exact C_id

#print axioms diagonal
#print axioms source_bounded_fresh
end models
end PA194SourceDiagonalPreservation
