import PA194FormulaAgreement
import PA194DualQuantRecursion
/-! Connect the canonical formula closer to the dual quantifier wrapper and
to the universal branch of the source traversal. The source translation's
recursive outputs are assumed well formed, not proved so here. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194CanonicalDualForall
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194FormulaAgreement PA194InternalFormulaClose PA194DualForallCode PA194DualQuantRecursion
  PA194TagDecoder PA194ChildCodes
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def canonical : Code 2 :=
  dualForallCode PA194TermWellFormedUnconditional.canonicalFirst
    PA194TermWellFormedUnconditional.canonicalSecond canonicalCloseFormula
/-- The actual dual source traversal instantiated with canonical closing. -/
noncomputable def translation (tag firstChild secondChild : Code 1) : Code 1 :=
  dualQuantTranslation tag PA194TermWellFormedUnconditional.canonicalFirst
    PA194TermWellFormedUnconditional.canonicalSecond firstChild secondChild canonicalCloseFormula

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

theorem canonical_equation (label positive negative : M)
    (hp : IsSemiformula ℒₒᵣ 0 positive) (hn : IsSemiformula ℒₒᵣ 0 negative) :
    F canonical ![label,pair positive negative] =
      pair (^∀ (PA194InternalFormulaClose.close label 0 positive))
        (^∃ (PA194InternalFormulaClose.close label 0 negative)) := by
  have hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val)
      PA194TermWellFormedUnconditional.canonicalFirst := (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  have hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val)
      PA194TermWellFormedUnconditional.canonicalSecond := (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  rw [canonical,modelDualForallInternal _ _ _ hf hs,
    pi₁_pair,pi₂_pair,canonical_close_agree label positive hp,canonical_close_agree label negative hn]

theorem canonical_wellformed (label positive negative : M)
    (hp : IsSemiformula ℒₒᵣ 0 positive) (hn : IsSemiformula ℒₒᵣ 0 negative) :
    let out := F canonical ![label,pair positive negative]
    IsSemiformula ℒₒᵣ 0 (π₁ out) ∧ IsSemiformula ℒₒᵣ 0 (π₂ out) := by
  dsimp only
  rw [canonical_equation label positive negative hp hn,pi₁_pair,pi₂_pair]
  constructor
  · apply IsSemiformula.all.mpr
    simpa using PA194InternalFormulaClose.close_wellformed label 0 positive hp
  · apply IsSemiformula.exs.mpr
    simpa using PA194InternalFormulaClose.close_wellformed label 0 negative hn

/-- At a source universal node, assuming the two recursively translated bodies
are internally well formed, the explicit compiler branch returns the exact
Foundation quantifier wrappers around the two internal closings. -/
theorem translation_universal (tag firstChild secondChild : Code 1)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label body : M)
    (hp : IsSemiformula ℒₒᵣ 0 (π₁ (F (translation tag firstChild secondChild) (fun _ => body))))
    (hn : IsSemiformula ℒₒᵣ 0 (π₂ (F (translation tag firstChild secondChild) (fun _ => body)))) :
    F (translation tag firstChild secondChild) (fun _ => 4 * cantor body label + 2) =
      pair (^∀ (PA194InternalFormulaClose.close label 0
        (π₁ (F (translation tag firstChild secondChild) (fun _ => body)))))
        (^∃ (PA194InternalFormulaClose.close label 0
        (π₂ (F (translation tag firstChild secondChild) (fun _ => body))))) := by
  have hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val)
      PA194TermWellFormedUnconditional.canonicalFirst := (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  have hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val)
      PA194TermWellFormedUnconditional.canonicalSecond := (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  rw [translation,modelDualQuantUniversal tag _ _ firstChild secondChild canonicalCloseFormula
    htag hf hs hfirst hsecond label body]
  change pair (^∀ (F canonicalCloseFormula ![label,π₁ (F (translation tag firstChild secondChild) (fun _ => body))]))
    (^∃ (F canonicalCloseFormula ![label,π₂ (F (translation tag firstChild secondChild) (fun _ => body))])) = _
  rw [canonical_close_agree label _ hp, canonical_close_agree label _ hn]
  rfl

#print axioms translation_universal
#print axioms canonical_equation
#print axioms canonical_wellformed
end models
end PA194CanonicalDualForall
