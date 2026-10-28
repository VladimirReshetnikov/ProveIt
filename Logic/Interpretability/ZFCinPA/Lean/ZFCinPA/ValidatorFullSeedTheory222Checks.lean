import ZFCinPA.ValidatorFullSeedTheory222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorFullSeedTheory222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorSourceFullSeed222 ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorEnvironmentStreams222 ValidatorEnvironmentVacuity222 ValidatorEnvironmentAlpha222
open ValidatorFullSeedTheory222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def sparseMatrix : SetTheorySemiproposition 2 :=
  ∀⁰ (FirstOrder.Semiformula.rel Language.Mem.mem
    ![(#0 : SyntacticSemiterm ℒₛₑₜ 3),&17] ⋏
      FirstOrder.Semiformula.nrel Language.Eq.eq ![#2,&31])

example : (⌜sparseMatrix⌝ : ℕ)≤seedRecognizerBodyVal (⌜sparseMatrix⌝ : ℕ) :=
  recognizerBody_quote_bound sparseMatrix
example : (⌜(⊤ : SetTheorySemiproposition 2)⌝ : ℕ)≤
    seedRecognizerBodyVal (⌜(⊤ : SetTheorySemiproposition 2)⌝ : ℕ) :=
  recognizerBody_quote_bound ⊤
example : (⌜(⊥ : SetTheorySemiproposition 2)⌝ : ℕ)≤
    seedRecognizerBodyVal (⌜(⊥ : SetTheorySemiproposition 2)⌝ : ℕ) :=
  recognizerBody_quote_bound ⊥

example (K : SetTheorySemiproposition 2) :
    (fullSeedBodyMeta K).univCl ∈ seedSchema := ⟨K,rfl⟩
example (K : SetTheorySemiproposition 2) :
    seedRecognizerBodyVal (⌜K⌝ : V)=(⌜fullSeedBodyMeta (∼K)⌝ : V) :=
  recognizerBody_quote K
example (p : V) : (V ⊧/![p] seedCh.val) ↔ SeedR p := by simp


example (m b s : V) (hb : IsSemiformula ℒₛₑₜ m b)
    (hshift : shift ℒₛₑₜ b=b)
    (h : ∀ F : V, StreamFree s F →
      CProv (encode F 0 s (subst ℒₛₑₜ (fvarVec m) b))) :
    ∀ F : V, StreamFree s F → CProv (encode F 0 s (qqAlls b m)) :=
  closure_image hb hshift h

/-- All free parameters are closed, including the nested sparse example. -/
theorem parameterized_closed_seed (K : SetTheorySemiproposition 2) (F s : V)
    (hs : StreamFree s F) :
    CProv (encode F 0 s (⌜(fullSeedBodyMeta K).univCl⌝ : V)) := by
  apply axOK_seedSchema _ (by simp) _ F s hs
  exact Δ₁Class.mem_iff.mpr ⟨K,rfl⟩

theorem sparse_closed_seed (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 s (⌜(fullSeedBodyMeta sparseMatrix).univCl⌝ : V)) :=
  parameterized_closed_seed sparseMatrix F s hs

example : seedTheory = ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪
    Set.range (fun K : SetTheorySemiproposition 2 => (fullSeedBodyMeta K).univCl) := rfl

example (p F s : V) (hp : SeedR p) (hs : StreamFree s F) :
    CProv (encode F 0 (s+2) p) := recognized_seed_image hp F (s+2) (streamFree_next hs)
example (p : V) (hp : SeedR p) : CProv (encode 0 0 2 p) :=
  recognized_seed_image hp 0 2 (streamFree_of_bounds (by simp) (by simp))
example (p F s : V) (hp : IsFormula ℒₛₑₜ p) (hm : p∈seedTheory.Δ₁Class)
    (hs : StreamFree s F) : CProv (encode F 0 s p) := axOK_seedTheory p hp hm F s hs
example (h : Provable seedTheory (^⊥ : V)) :
    ∃ d : V, ArithmeticHistory222.value d=2 := seedTheory_refutation_witness h

#print axioms parameterized_closed_seed
#print axioms sparse_closed_seed
#print axioms seedSchema_eq_negRange
#print axioms recognizerBody_quote
#print axioms recognizerBody_quote_bound
#print axioms recognizerBody_defined
#print axioms seedR_defined
#print axioms seedSchema_delta1
#print axioms closure_image
#print axioms recognized_seed_image
#print axioms axOK_seedSchema
#print axioms axOK_seedTheory
#print axioms seedTheory_refutation_witness
end LeanProofs.ZFCinPA.ValidatorFullSeedTheory222Checks
