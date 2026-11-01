import DiophantineConsistency.IPRAInductionGGBody
/-! Universal parameter closure of the actual GG induction-body equivalence.
The syntax remains free-variable `univCl'`; identification with the native
finite-parameter induction schema is a separate obligation. -/
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAClosure
variable {L : Language} {Λ : Hilbertᵢ L}
theorem allClosure_fixitr_iff {p q : Propositionᵢ L} (h : Λ ⊢ p 🡘 q) :
    (m : ℕ) → Λ ⊢ (∀⁰* (Rew.fixitr 0 m ▹ p)) 🡘 (∀⁰* (Rew.fixitr 0 m ▹ q))
  | 0 => by simpa using h
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    obtain ⟨h⟩ := allClosure_fixitr_iff h m
    apply Nonempty.intro
    apply HilbertProofᵢ.allIffAllOfIff
    simpa using h
theorem closed_gg_succInd_body {L : Language} [L.ORing] [L.DecidableEq]
    {Λ : Hilbertᵢ L} (φ : Semiformula L ℕ 1) (m : ℕ) :
    Λ ⊢ (∀⁰* (Rew.fixitr 0 m ▹
      ((φᴺ/[‘0’]) 🡒 (∀⁰ ((φᴺ/[#0]) 🡒 (φᴺ/[‘(#0 + 1)’]))) 🡒 ∀⁰ (φᴺ/[#0])))) 🡘
    (∀⁰* (Rew.fixitr 0 m ▹ Arithmetic.succInd φ))ᴺ := by
  simpa only [IPRAQuantifierFree.gg_allClosure, ← Semiformula.rew_doubleNegation] using
    (allClosure_fixitr_iff (IPRAImplicationBridge.gg_succInd_native_body (Λ := Λ) φ) m)
theorem univCl_gg_succInd_body {L : Language} [L.ORing] [L.DecidableEq]
    {Λ : Hilbertᵢ L} (φ : Semiformula L ℕ 1) :
    Λ ⊢ (∀⁰* (Rew.fixitr 0 (Arithmetic.succInd φ).fvSup ▹
      ((φᴺ/[‘0’]) 🡒 (∀⁰ ((φᴺ/[#0]) 🡒 (φᴺ/[‘(#0 + 1)’]))) 🡒 ∀⁰ (φᴺ/[#0])))) 🡘
    (Arithmetic.succInd φ).univCl'ᴺ := by
  simpa only [Semiformula.univCl'] using
    (closed_gg_succInd_body (Λ := Λ) φ (Arithmetic.succInd φ).fvSup)
end DiophantineConsistency.IPRAClosure
