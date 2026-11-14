import PA194TermRecursion
import PA194CloseRew
import PA194CloseBounded
/-! The single closing code on external finite shapes and standard quoted terms. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194TermQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CloseVariable PA194CloseRew PA194CloseBounded

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

theorem modelShape (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M) (t : Shape M) :
    F (PA194TermRecursion.closeCode first second) ![t.encoded,label,depth] = t.closed label depth := by
  induction t with
  | bound i => exact PA194TermRecursion.modelCloseBound first second hf hs i label depth
  | free i => exact PA194TermRecursion.modelCloseFree first second hf hs i label depth
  | nullary f => exact PA194TermRecursion.modelCloseNullary first second hf hs f label depth
  | unary f x ih =>
    simpa [Shape.encoded, Shape.closed,PA194CloseFunction.vec,ih] using
      PA194TermRecursion.modelCloseUnary first second hf hs f x.encoded label depth
  | binary f x y ihx ihy =>
    simpa [Shape.encoded, Shape.closed,PA194CloseFunction.vec,ihx,ihy] using
      PA194TermRecursion.modelCloseBinary first second hf hs f x.encoded y.encoded label depth


/-- The syntax and its label and binder depth are external standard objects. -/
theorem quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (a d : Nat) (t : Semiterm ℒₒᵣ Nat d) :
    F (PA194TermRecursion.closeCode first second) ![(⌜t⌝ : M),(a : M),(d : M)] =
      (⌜closeDepthRew a d t⌝ : M) := by
  induction t with
  | bvar i =>
    rw [Semiterm.quote_bvar]
    simp only [qqBvar]
    rw [PA194TermRecursion.modelCloseBound first second hf hs]
    simpa only [modelCloseBoundInternal, qqBvar] using (modelCloseBoundQuote (M := M) a d i)
  | fvar x =>
    rw [Semiterm.quote_fvar]
    simp only [qqFvar]
    rw [PA194TermRecursion.modelCloseFree first second hf hs]
    simpa only [modelCloseFreeInternal, qqBvar, qqFvar] using (modelCloseFreeQuote (M := M) a x d)
  | @func k f v ih =>
    rw [Semiterm.quote_func, Rew.func, Semiterm.quote_func]
    simp only [qqFunc, SemitermVec.val, matrixToVec, adjoin_def]
    cases f <;> simp_all
    case zero => exact PA194TermRecursion.modelCloseNullary first second hf hs _ _ _
    case one => exact PA194TermRecursion.modelCloseNullary first second hf hs _ _ _
    case add =>
      change F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 2 (pair _ (pair (⌜v 0⌝ : M) (pair (⌜v 1⌝ : M) 0+1)+1)))+1,_,_] = _
      rw [PA194TermRecursion.modelCloseBinary first second hf hs, ih.1, ih.2]
      rfl
    case mul =>
      change F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 2 (pair _ (pair (⌜v 0⌝ : M) (pair (⌜v 1⌝ : M) 0+1)+1)))+1,_,_] = _
      rw [PA194TermRecursion.modelCloseBinary first second hf hs, ih.1, ih.2]
      rfl

#print axioms modelShape
#print axioms quote
end models
end PA194TermQuote
