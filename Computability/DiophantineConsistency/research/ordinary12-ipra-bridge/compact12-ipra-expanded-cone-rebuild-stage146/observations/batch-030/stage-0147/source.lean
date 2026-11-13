import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
import DiophantineConsistency.FoundationPAHFSyntax
import DiophantineConsistency.HABasicArithmetic

/-! Exact universal closure for the existing classical Foundation source,
its existing GG translation, and the conventional HA syntax. -/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAClosure
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax

theorem doubleNegation_allClosure {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) :
    (∀⁰* φ)ᴺ = ∀⁰* φᴺ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [allClosure_succ, Semiformula.doubleNegation_all] using ih (∀⁰ φ)

theorem formula_allClosure {n : ℕ} (φ : Semiformulaᵢ ℒₒᵣ ℕ n) :
    formula (∀⁰* φ) = SetTheory.PA.Formula.closeN n (formula φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allClosure_succ, ih]
    rw [show formula (∀⁰ φ) = SetTheory.PA.Formula.all (formula φ) from formula_all φ]
    rfl

/-- Canonical target slots agree both for newly bound variables and for
remaining free variables, even if the closure count does not cover them. -/
theorem formula_fixitr (m : ℕ) (φ : Semiformulaᵢ ℒₒᵣ ℕ 0) :
    formula (Rew.fixitr 0 m ▹ φ) = formula φ := by
  unfold formula
  rw [formulaAux_rew]
  congr 1
  · funext i
    exact Fin.elim0 i
  · funext x
    rw [Rew.fixitr_fvar]
    split_ifs with hx
    · rfl
    · simp only [termAux, Nat.zero_add]
      congr 1
      omega

/-- This is Foundation's actual `fvSup/fixitr/allClosure/toEmpty` closure,
not a replacement closure convention. -/
theorem sentence_univCl (φ : Proposition ℒₒᵣ) :
    sentence (Semiformula.univCl φ)ᴺ =
      SetTheory.PA.Formula.closeN φ.fvSup (formula φᴺ) := by
  unfold sentence
  rw [Semiformula.emb_doubleNegation]
  change formula ((Semiformula.univCl φ : Proposition ℒₒᵣ)ᴺ) = _
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl',
    doubleNegation_allClosure, ← Semiformula.rew_doubleNegation,
    formula_allClosure, formula_fixitr]
  simp only [Nat.zero_add]

/-- Closing an actual HA proof supplies every parameter quantifier in the
literal translated source axiom. This constructs a proof, not model truth. -/
theorem proves_univCl (φ : Proposition ℒₒᵣ) (h : HA.Proves (formula φᴺ)) :
    HA.Proves (sentence (Semiformula.univCl φ)ᴺ) := by
  rw [sentence_univCl]
  exact HA.Arithmetic.reclose φ.fvSup h

end DiophantineConsistency.FoundationHAClosure
