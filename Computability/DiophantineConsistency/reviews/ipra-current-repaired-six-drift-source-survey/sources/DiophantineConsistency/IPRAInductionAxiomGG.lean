import DiophantineConsistency.IPRAInductionQMatrix
import DiophantineConsistency.IPRAInductionRewNatural
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency.IPRAMatrixQ DiophantineConsistency.IPRARewNatural
open DiophantineConsistency.IPRANativeInduction
set_option autoImplicit false
namespace DiophantineConsistency.IPRABodyBinding
open PRALanguage PRATheory LO.Entailment
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem embedded_body (φ : Semiformula language ℕ 1) :
    (Rewriting.emb (inductionBody (finiteMatrix φ)ᴺ) : Semiformulaᵢ language ℕ (0 + (succInd φ).fvSup)) =
    Rew.fixitr 0 (succInd φ).fvSup ▹
      ((φᴺ/[‘0’]) 🡒 (∀⁰ ((φᴺ/[#0]) 🡒 (φᴺ/[‘(#0 + 1)’]))) 🡒 ∀⁰ (φᴺ/[#0])) := by
  rw [body_natural]
  simp [inductionBody, atZero, atStep, Rewriting.emb_subst_eq_subst_emb,
    emb_gg_finiteMatrix, zeroTerm, stepTerm]
  constructor <;> congr 2 <;> funext i <;> cases i using Fin.cases <;>
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Add.term_eq, Rew.func, Function.comp_def]
  · change (Semiterm.func (L := language) (PRAFiniteFunctionCodes.Code.zero 0) (fun x => Rew.emb (Fin.elim0 x))) =
      Rew.subst ![] (Rew.emb (Semiterm.func (L := language) (PRAFiniteFunctionCodes.Code.zero 0) ![]))
    simp [Rew.func, Function.comp_def]
    all_goals funext i; exact Fin.elim0 i
  · constructor
    · rfl
    · funext x
      cases x using Fin.cases with
      | zero => simp
      | succ x =>
        cases x using Fin.cases with
        | zero =>
          change Rew.emb (Semiterm.func (L := language) oneCode Fin.elim0) =
            Rew.subst ![] (Rew.emb (Semiterm.func (L := language) oneCode ![]))
          simp [Rew.func, Function.comp_def]
          all_goals funext i; exact Fin.elim0 i
        | succ x => exact Fin.elim0 x
theorem embedded_axiom (φ : Semiformula language ℕ 1) :
    (Rewriting.emb (inductionAxiom (finiteMatrix φ)ᴺ) : Propositionᵢ language) =
    ∀⁰* (Rew.fixitr 0 (succInd φ).fvSup ▹
      ((φᴺ/[‘0’]) 🡒 (∀⁰ ((φᴺ/[#0]) 🡒 (φᴺ/[‘(#0 + 1)’]))) 🡒 ∀⁰ (φᴺ/[#0]))) := by
  simp only [inductionAxiom, Rewriting.emb_allClosure, embedded_body]
theorem induction_gg_in_theory
    (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ nativeInduction, σ ∈ T) (φ : Semiformula language ℕ 1) (hφ : φ.Open) :
    T ⊢ (succInd φ).univClᴺ := by
  let ax := inductionAxiom (finiteMatrix φ)ᴺ
  have hAx : T ⊢! ax := Entailment.byAxm (hax ax (native_matrix_instance φ hφ))
  have hEquiv : (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      (Rewriting.emb ax : Propositionᵢ language) 🡘
      (Rewriting.emb ((succInd φ).univClᴺ) : Propositionᵢ language) := by
    simpa only [ax, embedded_axiom, Semiformula.emb_doubleNegation,
      Semiformula.coe_univCl_eq_univCl'] using
        (IPRAClosure.univCl_gg_succInd_body (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) φ)
  obtain ⟨hEq⟩ := hEquiv
  exact ⟨Context.mdp (Context.of (Entailment.K_left hEq)) hAx⟩
theorem induction_scheme_gg_in_theory
    (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ nativeInduction, σ ∈ T)
    (σ : Sentence language) (hσ : σ ∈ InductionScheme language Semiformula.Open) :
    T ⊢ σᴺ := by
  obtain ⟨φ, hφ, rfl⟩ := hσ
  exact induction_gg_in_theory T hax φ hφ
end DiophantineConsistency.IPRABodyBinding
