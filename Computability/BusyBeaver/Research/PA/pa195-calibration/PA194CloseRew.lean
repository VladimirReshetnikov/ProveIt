import PA194CloseVariable
import PA194BindTranslation
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding
set_option autoImplicit false
namespace PA194CloseRew
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def closeDepthRew (a : Nat) : (d : Nat) → Rew ℒₒᵣ Nat d Nat (d+1)
  | 0 => Rew.bind Fin.elim0 (fun z => if z = a then #0 else &z)
  | d+1 => (closeDepthRew a d).q

theorem closeDepthRew_fvar (a d z : Nat) :
    closeDepthRew a d &z = if z = a then #(Fin.last d) else &z := by
  induction d with
  | zero => simp [closeDepthRew,Rew.bind_fvar]
  | succ d ih =>
    rw [closeDepthRew,Rew.q_fvar,ih]
    split <;> simp_all

theorem closeDepthRew_bvar (a d : Nat) (i : Fin d) :
    closeDepthRew a d #i = #(Fin.castSucc i) := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    cases i using Fin.cases with
    | zero => simp [closeDepthRew]
    | succ j =>
      rw [closeDepthRew,Rew.q_bvar_succ,ih]
      simp
theorem closeDepthRew_formula_zero (a : Nat) (φ : ArithmeticFormula Nat) :
    closeDepthRew a 0 ▹ φ = PA194BindTranslation.closeLabel a φ := rfl

section models
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PA194CloseVariable
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelCloseFreeQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a z d : Nat) :
    F closeFreeCode ![(a : M),(z : M),(d : M)] =
      (⌜closeDepthRew a d &z⌝ : M) := by
  rw [modelCloseFreeInternal,closeDepthRew_fvar]
  by_cases h : z = a
  · subst z
    simp [Semiterm.quote_bvar,qqBvar]
  · have h' : (a : M) ≠ (z : M) := by
      intro he
      exact h (Nat.cast_injective he).symm
    simp [h,h',Semiterm.quote_fvar,qqFvar]

theorem modelCloseBoundQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a d : Nat) (i : Fin d) :
    F closeBoundCode ![(d : M),(i.val : M)] =
      (⌜closeDepthRew a d #i⌝ : M) := by
  rw [modelCloseBoundInternal,closeDepthRew_bvar]
  have hi : (i.val : M) < (d : M) := by exact_mod_cast i.isLt
  simp [hi,Semiterm.quote_bvar,qqBvar]

#print axioms closeDepthRew_fvar
#print axioms closeDepthRew_bvar
#print axioms closeDepthRew_formula_zero
#print axioms modelCloseFreeQuote
#print axioms modelCloseBoundQuote
end models
end PA194CloseRew
