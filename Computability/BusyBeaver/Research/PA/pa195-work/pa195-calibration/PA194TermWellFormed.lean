import PA194TermRecursion
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Typed
/-! Conditional well-formedness for arbitrary model-internal arithmetic terms. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194TermWellFormed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
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

/-- The definability hypothesis is explicit and is not discharged here. -/
theorem internal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M)
    (hdef : 𝚺₁-Predicate (fun t : M => IsSemiterm ℒₒᵣ (depth + 1) (F (PA194TermRecursion.closeCode first second) ![t,label,depth])))
    (t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ (depth + 1) (F (PA194TermRecursion.closeCode first second) ![t,label,depth]) := by
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz
    simp only [qqBvar]
    rw [PA194TermRecursion.modelCloseBound first second hf hs, if_pos hz]
    change IsSemiterm ℒₒᵣ (depth+1) (^#z)
    simp only [IsSemiterm.bvar]
    exact lt_trans hz (lt_add_one depth)
  · intro x
    simp only [qqFvar]
    rw [PA194TermRecursion.modelCloseFree first second hf hs]
    split
    · change IsSemiterm ℒₒᵣ (depth+1) (^#depth)
      simp
    · change IsSemiterm ℒₒᵣ (depth+1) (^&x)
      exact IsSemiterm.fvar _ _
  · intro k f v hfunc hv ih
    have hk : k = 0 ∨ k = 2 := by
      rcases (Arithmetic.isFunc_iff_LOR (V := M)).mp hfunc with (⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩)
      all_goals simp_all
    rcases hk with rfl | rfl
    · have hv0 : v = 0 := IsSemitermVec.empty_iff.mp hv
      subst v
      change IsSemiterm ℒₒᵣ (depth+1) (F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 0 (pair f 0))+1,label,depth])
      rw [PA194TermRecursion.modelCloseNullary first second hf hs]
      change IsSemiterm ℒₒᵣ (depth+1) (^func 0 f 0)
      exact IsSemiterm.func.mpr ⟨hfunc, IsSemitermVec.empty _⟩
    · obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
      have ihx : IsSemiterm ℒₒᵣ (depth+1) (F (PA194TermRecursion.closeCode first second) ![x,label,depth]) := by
        simpa using ih 0 (by norm_num)
      have ihy : IsSemiterm ℒₒᵣ (depth+1) (F (PA194TermRecursion.closeCode first second) ![y,label,depth]) := by
        simpa using ih 1 (by norm_num)
      change IsSemiterm ℒₒᵣ (depth+1) (F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 2 (pair f (pair x (pair y 0+1)+1)))+1,label,depth])
      rw [PA194TermRecursion.modelCloseBinary first second hf hs]
      change IsSemiterm ℒₒᵣ (depth+1) (^func 2 f ?[F (PA194TermRecursion.closeCode first second) ![x,label,depth], F (PA194TermRecursion.closeCode first second) ![y,label,depth]])
      exact IsSemiterm.func.mpr ⟨hfunc, IsSemitermVec.doubleton.mpr ⟨ihx,ihy⟩⟩

/-- A Σ₁-definable unary output function supplies the predicate required above. -/
theorem predicate_of_function [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (g : M → M) (depth : M)
    (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun t : M => IsSemiterm ℒₒᵣ (depth+1) (g t)) := by
  exact HierarchySymbol.Definable.comp₂ (P := IsSemiterm ℒₒᵣ)
    (HierarchySymbol.DefinableFunction.const (depth+1)) hg

/-- The remaining assumption can also be supplied at the function level. -/
theorem internal_of_function [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M)
    (hcode : 𝚺₁-Function₁ (fun t : M => F (PA194TermRecursion.closeCode first second) ![t,label,depth]))
    (t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ (depth + 1) (F (PA194TermRecursion.closeCode first second) ![t,label,depth]) := by
  exact internal first second hf hs label depth (predicate_of_function _ depth hcode) t ht

#print axioms internal
#print axioms predicate_of_function
#print axioms internal_of_function
end models
end PA194TermWellFormed
