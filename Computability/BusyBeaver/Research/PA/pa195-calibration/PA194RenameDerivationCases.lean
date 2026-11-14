import PA194RenameContexts
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Conditional preservation for each Foundation internal derivation rule.
No recursion over whole derivations is established in this file. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194RenameDerivationCases
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution PA194RenameContexts
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
variable (mapGraph : 𝚺₁.Semisentence 3) (f : M → M → M)
variable (hf : ∀ v : Fin 3 → M, (M ⊧/v mapGraph.val) ↔ v 0 = f (v 2) (v 1))

lemma image_mem (p x s : M) (hx : x ∈ s) :
    renameFormula mapGraph f hf p x ∈ renameSet mapGraph f hf p s :=
  (mem_renameSet_iff mapGraph f hf).mpr ⟨x,hx,rfl⟩

lemma root_rule (p φ s : M) (hs : IsFormulaSet ℒₒᵣ s) (hmem : φ ∈ s)
    (haxiom : φ ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  apply Derivable.by_axm (renameSet_wf mapGraph f hf p s hs) φ
  · rw [← pa_axiom_fixed mapGraph f hf p φ haxiom]
    exact image_mem mapGraph f hf p φ s hmem
  · exact haxiom

lemma axl_rule (p φ s : M) (hs : IsFormulaSet ℒₒᵣ s) (hmem : φ ∈ s) (hneg : neg ℒₒᵣ φ ∈ s) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  apply Derivable.em (renameSet_wf mapGraph f hf p s hs) (renameFormula mapGraph f hf p φ)
  · exact image_mem mapGraph f hf p φ s hmem
  · rw [← formula_neg mapGraph f hf p 0 φ (hs φ hmem)]
    exact image_mem mapGraph f hf p (neg ℒₒᵣ φ) s hneg

lemma verum_rule (p s : M) (hs : IsFormulaSet ℒₒᵣ s) (hmem : ^⊤ ∈ s) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  apply Derivable.verum (renameSet_wf mapGraph f hf p s hs)
  rw [← rename_verum mapGraph f hf p]
  exact image_mem mapGraph f hf p ^⊤ s hmem

lemma and_rule (p φ ψ s : M) (hφ : IsUFormula ℒₒᵣ φ) (hψ : IsUFormula ℒₒᵣ ψ)
    (hmem : φ ^⋏ ψ ∈ s)
    (hleft : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert φ s)))
    (hright : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert ψ s))) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  have hm : renameFormula mapGraph f hf p φ ^⋏ renameFormula mapGraph f hf p ψ ∈ renameSet mapGraph f hf p s := by
    rw [← rename_and mapGraph f hf p φ ψ hφ hψ]
    exact image_mem mapGraph f hf p (φ ^⋏ ψ) s hmem
  apply Derivable.and_m hm
  · simpa [renameSet_insert] using hleft
  · simpa [renameSet_insert] using hright

lemma or_rule (p φ ψ s : M) (hφ : IsUFormula ℒₒᵣ φ) (hψ : IsUFormula ℒₒᵣ ψ)
    (hmem : φ ^⋎ ψ ∈ s)
    (hpremise : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert φ (insert ψ s)))) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  have hm : renameFormula mapGraph f hf p φ ^⋎ renameFormula mapGraph f hf p ψ ∈ renameSet mapGraph f hf p s := by
    rw [← rename_or mapGraph f hf p φ ψ hφ hψ]
    exact image_mem mapGraph f hf p (φ ^⋎ ψ) s hmem
  apply Derivable.or_m hm
  simpa [renameSet_insert] using hpremise

lemma image_subset (p s t : M) (hst : s ⊆ t) : renameSet mapGraph f hf p s ⊆ renameSet mapGraph f hf p t := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := (mem_renameSet_iff mapGraph f hf).mp hy
  exact image_mem mapGraph f hf p x t (hst hx)

lemma wk_rule (p s t : M) (ht : IsFormulaSet ℒₒᵣ t) (hst : s ⊆ t)
    (hpre : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s)) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p t) :=
  Derivable.wk (renameSet_wf mapGraph f hf p t ht) (image_subset mapGraph f hf p s t hst) hpre

lemma cut_rule (p φ s : M) (hφ : IsFormula ℒₒᵣ φ)
    (hleft : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert φ s)))
    (hright : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert (neg ℒₒᵣ φ) s))) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  apply Derivable.cut (renameFormula mapGraph f hf p φ)
  · simpa [renameSet_insert] using hleft
  · simpa [renameSet_insert, formula_neg mapGraph f hf p 0 φ hφ] using hright

lemma renameVec_single (p t : M) (ht : IsTerm ℒₒᵣ t) :
    renameVec mapGraph f hf p 1 (?[t] : M) = ?[renameTerm mapGraph f hf p t] := by
  unfold renameVec
  rw [show (1 : M) = 0+1 by simp,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) ht.isUTerm]
  simp [renameTerm]

lemma ex_rule (p φ t s : M) (hφ : IsSemiformula ℒₒᵣ 1 φ) (ht : IsTerm ℒₒᵣ t)
    (hmem : ^∃ φ ∈ s)
    (hpre : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert (substs1 ℒₒᵣ t φ) s))) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p s) := by
  have hmem' : ^∃ (renameFormula mapGraph f hf p φ) ∈ renameSet mapGraph f hf p s := by
    apply (mem_renameSet_iff mapGraph f hf).mpr
    refine ⟨^∃ φ, hmem, ?_⟩
    exact (rename_exs mapGraph f hf p φ hφ.isUFormula).symm
  have hterm : IsTerm ℒₒᵣ (renameTerm mapGraph f hf p t) := term_wf mapGraph f hf p 0 t ht
  apply Derivable.ex_m hmem' hterm
  rw [renameSet_insert] at hpre
  have hsubst : renameFormula mapGraph f hf p (substs1 ℒₒᵣ t φ) =
      substs1 ℒₒᵣ (renameTerm mapGraph f hf p t) (renameFormula mapGraph f hf p φ) := by
    unfold substs1
    rw [formula_rename_subst mapGraph f hf p 1 φ hφ 0 ?[t] (by simpa using ht),
      renameVec_single mapGraph f hf p t ht]
  simpa [hsubst] using hpre

lemma shift_rule (p q s : M) (hs : IsFormulaSet ℒₒᵣ s)
    (hmap : ∀ x, f p (x+1) = f q x+1)
    (hpre : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf q s)) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (setShift ℒₒᵣ s)) := by
  rw [renameSet_shift mapGraph f hf p q s hs hmap]
  exact hpre.shift

lemma shift_rule_noshift (p q s : M) (hs : IsFormulaSet ℒₒᵣ s)
    (hmap : ∀ x, f p (x+1) = f q x)
    (hpre : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf q s)) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (setShift ℒₒᵣ s)) := by
  rwa [renameSet_shift_noshift mapGraph f hf p q s hs hmap]

lemma all_rule (p q φ s : M) (hφ : IsSemiformula ℒₒᵣ 1 φ) (hs : IsFormulaSet ℒₒᵣ s)
    (hmem : ^∀ φ ∈ s) (hzero : f p 0 = 0) (hmap : ∀ x, f p (x+1) = f q x+1)
    (hpre : Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf p (insert (free ℒₒᵣ φ) (setShift ℒₒᵣ s)))) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (renameSet mapGraph f hf q s) := by
  have hmem' : ^∀ (renameFormula mapGraph f hf q φ) ∈ renameSet mapGraph f hf q s := by
    apply (mem_renameSet_iff mapGraph f hf).mpr
    refine ⟨^∀ φ, hmem, ?_⟩
    exact (rename_all mapGraph f hf q φ hφ.isUFormula).symm
  have hpre' : Derivable (𝗣𝗔 : ArithmeticTheory)
      (insert (free ℒₒᵣ (renameFormula mapGraph f hf q φ)) (setShift ℒₒᵣ (renameSet mapGraph f hf q s))) := by
    simpa [renameSet_allPremise mapGraph f hf p q φ s hφ hs hzero hmap] using hpre
  exact Derivable.all_m hmem' hpre'

#print axioms root_rule
#print axioms axl_rule
#print axioms verum_rule
#print axioms and_rule
#print axioms or_rule
#print axioms wk_rule
#print axioms cut_rule
#print axioms ex_rule
#print axioms shift_rule
#print axioms shift_rule_noshift
#print axioms all_rule
end models
end PA194RenameDerivationCases
