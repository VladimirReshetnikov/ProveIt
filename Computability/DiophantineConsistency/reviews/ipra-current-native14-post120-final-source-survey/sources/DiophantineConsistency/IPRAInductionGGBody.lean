import DiophantineConsistency.IPRANativeInduction
/-! The exact free-parameter Foundation successor-induction body translates to
an intuitionistic implication-shaped body. Closure and native-theory axiom
transfer are separate obligations. -/
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAImplicationBridge
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

theorem gg_two_implications (p q r : Proposition L) :
    Λ ⊢ (pᴺ 🡒 qᴺ 🡒 rᴺ) 🡘 (p 🡒 q 🡒 r)ᴺ := by
  obtain ⟨h₁⟩ := Derivation.imply_doubleNegation (Λ := Λ) q r
  obtain ⟨h₂⟩ := Derivation.imply_doubleNegation (Λ := Λ) p (q 🡒 r)
  exact ⟨Entailment.E_trans (Entailment.ECC_of_E_of_E Entailment.E_Id h₁) h₂⟩
theorem gg_all_implication (p q : Semiformula L ℕ 1) :
    Λ ⊢ (∀⁰ (pᴺ 🡒 qᴺ)) 🡘 (∀⁰ (p 🡒 q))ᴺ := by
  obtain ⟨h⟩ := Derivation.imply_doubleNegation (Λ := Λ) (Rewriting.free p) (Rewriting.free q)
  apply Nonempty.intro
  apply HilbertProofᵢ.allIffAllOfIff
  exact Entailment.cast h (by simp [Semiformula.rew_doubleNegation])
theorem gg_induction_shape (base : Proposition L) (p q r : Semiformula L ℕ 1) :
    Λ ⊢ (baseᴺ 🡒 (∀⁰ (pᴺ 🡒 qᴺ)) 🡒 ∀⁰ rᴺ) 🡘
      (base 🡒 (∀⁰ (p 🡒 q)) 🡒 ∀⁰ r)ᴺ := by
  obtain ⟨hs⟩ := gg_all_implication (Λ := Λ) p q
  obtain ⟨ht⟩ := gg_two_implications (Λ := Λ) base (∀⁰ (p 🡒 q)) (∀⁰ r)
  exact ⟨Entailment.E_trans
    (Entailment.ECC_of_E_of_E Entailment.E_Id
      (Entailment.ECC_of_E_of_E hs Entailment.E_Id)) ht⟩
theorem gg_succInd_body {L : Language} [L.ORing] [L.DecidableEq]
    {Λ : Hilbertᵢ L} (φ : Semiformula L ℕ 1) :
    Λ ⊢ ((φ/[‘0’])ᴺ 🡒 (∀⁰ ((φ/[#0])ᴺ 🡒 (φ/[‘(#0 + 1)’])ᴺ)) 🡒
      ∀⁰ (φ/[#0])ᴺ) 🡘 (Arithmetic.succInd φ)ᴺ := by
  simpa only [Arithmetic.succInd] using
    (gg_induction_shape (Λ := Λ) (φ/[‘0’]) (φ/[#0]) (φ/[‘(#0 + 1)’]) (φ/[#0]))
theorem gg_succInd_native_body {L : Language} [L.ORing] [L.DecidableEq]
    {Λ : Hilbertᵢ L} (φ : Semiformula L ℕ 1) :
    Λ ⊢ ((φᴺ/[‘0’]) 🡒 (∀⁰ ((φᴺ/[#0]) 🡒 (φᴺ/[‘(#0 + 1)’]))) 🡒
      ∀⁰ (φᴺ/[#0])) 🡘 (Arithmetic.succInd φ)ᴺ := by
  simpa only [Semiformula.rew_doubleNegation] using (gg_succInd_body (Λ := Λ) φ)
end DiophantineConsistency.IPRAImplicationBridge
