import PA194SourcePolarity
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
/-! Model-uniform preservation of the named-source modus-ponens rule by
internal PA provability. This does not provide a proof-code transformer. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194SourceMPPreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194TagDecoder PA194ChildCodes PA194SourceOutputWF PA194SourcePolarity
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

/-- For nonzero implication code, the positive translation is the internal
implication of the positive translations. -/
theorem implication_code (a b : M) (hnz : 4*cantor a b ≠ 0) :
    let pa := π₁ (F fixedTranslation (fun _ => a))
    let pb := π₁ (F fixedTranslation (fun _ => b))
    π₁ (F fixedTranslation (fun _ => 4*cantor a b)) = imp ℒₒᵣ pa pb := by
  dsimp only
  have hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val)
      PA194TermWellFormedUnconditional.canonicalFirst := (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  have hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val)
      PA194TermWellFormedUnconditional.canonicalSecond := (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  have ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) fixedTag :=
    (Classical.choose_spec PRA_has_tagCode).2
  have hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) fixedFirst :=
    (Classical.choose_spec PRA_has_firstChildCode).2
  have hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) fixedSecond :=
    (Classical.choose_spec PRA_has_secondChildCode).2
  have hpol := fixed_all_pol (M := M) a
  change π₂ (F fixedTranslation (fun _ => a)) = neg ℒₒᵣ (π₁ (F fixedTranslation (fun _ => a))) at hpol
  have hm := modelDualImplication fixedTag PA194TermWellFormedUnconditional.canonicalFirst
    PA194TermWellFormedUnconditional.canonicalSecond fixedFirst fixedSecond PA194CanonicalDualForall.canonical
    ht hf hs hfirst hsecond a b hnz
  change F fixedTranslation (fun _ => 4*cantor a b) =
    pair (pair 5 (pair (π₂ (F fixedTranslation (fun _ => a))) (π₁ (F fixedTranslation (fun _ => b)))) + 1)
      (pair 4 (pair (π₁ (F fixedTranslation (fun _ => a))) (π₂ (F fixedTranslation (fun _ => b)))) + 1) at hm
  rw [hm,pi₁_pair,hpol]
  rfl

/-- A model-internal PA proof of each positive premise yields a model-internal
PA proof of the positive conclusion. The implication source code is nonzero. -/
theorem mp_nonzero (a b : M) (hnz : 4*cantor a b ≠ 0)
    (himp : Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => 4*cantor a b))))
    (ha : Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => a)))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => b))) := by
  let φ : Bootstrapping.Formula M ℒₒᵣ := ⟨π₁ (F fixedTranslation (fun _ => a)), (fixed_all_wf a).1⟩
  let ψ : Bootstrapping.Formula M ℒₒᵣ := ⟨π₁ (F fixedTranslation (fun _ => b)), (fixed_all_wf b).1⟩
  rw [implication_code a b hnz] at himp
  have hφ : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ φ := (tprovable_iff_provable).mpr ha
  have hφψ : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ φ 🡒 ψ := by
    apply (tprovable_iff_provable).mpr
    simpa [φ,ψ,Bootstrapping.Semiformula.imp_def, Bootstrapping.imp] using himp
  change Provable (𝗣𝗔 : ArithmeticTheory) ψ.val
  exact (tprovable_iff_provable).mp (hφψ ⨀ hφ)

/-- The source's zero implication is an alias: it forces both inputs to zero. -/
theorem implication_zero (a b : M) (h : 4*cantor a b = 0) : a = 0 ∧ b = 0 := by
  have hp : cantor a b = 0 := by
    rcases mul_eq_zero.mp h with hfour | hz
    · norm_num at hfour
    · exact hz
  apply cantor_injective
  simpa [cantor,triangle] using hp

/-- Source modus ponens preserves model-internal PA provability, including the
zero-code alias and arbitrary nonstandard source codes. -/
theorem mp (a b : M)
    (himp : Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => 4*cantor a b))))
    (ha : Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => a)))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => b))) := by
  by_cases hnz : 4*cantor a b = 0
  · obtain ⟨rfl,rfl⟩ := implication_zero a b hnz
    exact ha
  · exact mp_nonzero a b hnz himp ha

#print axioms mp
#print axioms implication_zero
#print axioms mp_nonzero
#print axioms implication_code
end models
end PA194SourceMPPreservation
