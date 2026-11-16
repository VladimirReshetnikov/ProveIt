import DiophantineConsistency.IPRAOpenSyntax
import DiophantineConsistency.PRATheory
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
/-! Quantifier-freeness under Gödel–Gentzen translation and the exact
intuitionistic image of an all-closed arithmetic nonzero equation. This
module does not assert the iPRA axiom transfer. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAQuantifierFree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder

theorem gg_preserves_open {L : Language} {ξ : Type} {n : ℕ}
    (φ : Semiformula L ξ n) (h : φ.Open) : OpenI φᴺ := by
  induction φ using Semiformula.rec' <;> simp_all [OpenI, Semiformula.doubleNegation]
theorem gg_allClosure {L : Language} {ξ : Type} {n : ℕ} (φ : Semiformula L ξ n) :
    (∀⁰* φ)ᴺ = ∀⁰* φᴺ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allClosure_succ]
    exact ih _

theorem gg_noZero (n : ℕ) (a b : PRATheory.TermN n) :
    (∀⁰* (Semiformula.nrel Language.ORing.Rel.eq ![a,b]))ᴺ =
      ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b])) := by
  simp [gg_allClosure]
end DiophantineConsistency.IPRAQuantifierFree
