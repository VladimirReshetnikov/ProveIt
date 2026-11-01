import DiophantineConsistency.IPRANativeBasicImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRATwoImpLogic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree
open IPRANativeTheory IPRANativeAxiomImage IPRANativeEquationImages IPRANativeBasicImages
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
theorem twoImp_dni (p q r : Propositionᵢ L) :
    Λ ⊢ (p 🡒 q 🡒 r) 🡒 (∼∼p 🡒 ∼∼q 🡒 ∼∼r) := by
  have h₁ : Λ ⊢! (p 🡒 q 🡒 r) 🡒 (p 🡒 ∼∼q 🡒 ∼∼r) :=
    Entailment.CCC_of_C_right Entailment.CCCNNNN
  have h₂ : Λ ⊢! (p 🡒 ∼∼q 🡒 ∼∼r) 🡒 (∼∼q 🡒 p 🡒 ∼∼r) := Entailment.CCCCC
  have h₃ : Λ ⊢! (∼∼q 🡒 p 🡒 ∼∼r) 🡒 (∼∼q 🡒 ∼∼p 🡒 ∼∼∼∼r) :=
    Entailment.CCC_of_C_right Entailment.CCCNNNN
  have h₄ : Λ ⊢! ∼∼∼∼r 🡒 ∼∼r := Entailment.contra Entailment.dni
  have h₅ : Λ ⊢! (∼∼q 🡒 ∼∼p 🡒 ∼∼∼∼r) 🡒 (∼∼q 🡒 ∼∼p 🡒 ∼∼r) :=
    Entailment.CCC_of_C_right (Entailment.CCC_of_C_right h₄)
  have h₆ : Λ ⊢! (∼∼q 🡒 ∼∼p 🡒 ∼∼r) 🡒 (∼∼p 🡒 ∼∼q 🡒 ∼∼r) := Entailment.CCCCC
  exact ⟨Entailment.C_trans h₁ (Entailment.C_trans h₂ (Entailment.C_trans h₃
    (Entailment.C_trans h₅ h₆)))⟩
theorem gg_two_implications (p q r : Proposition L) :
    Λ ⊢ (pᴺ 🡒 qᴺ 🡒 rᴺ) 🡘 (p 🡒 q 🡒 r)ᴺ := by
  obtain ⟨h₁⟩ := Derivation.imply_doubleNegation (Λ := Λ) q r
  obtain ⟨h₂⟩ := Derivation.imply_doubleNegation (Λ := Λ) p (q 🡒 r)
  exact ⟨Entailment.E_trans (Entailment.ECC_of_E_of_E Entailment.E_Id h₁) h₂⟩
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem atomic_twoImp_image (n : ℕ) {k j l : ℕ} (r : language.Rel k)
    (s : language.Rel j) (t : language.Rel l)
    (v : Fin k → Semiterm language ℕ n) (w : Fin j → Semiterm language ℕ n)
    (u : Fin l → Semiterm language ℕ n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      openAll n ((Semiformulaᵢ.rel r v) 🡒 (Semiformulaᵢ.rel s w) 🡒 Semiformulaᵢ.rel t u) 🡒
      openAll n (((Semiformula.rel r v) 🡒 (Semiformula.rel s w) 🡒 Semiformula.rel t u)ᴺ) := by
  have h := gg_two_implications (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (openAllC n (Semiformula.rel r v)) (openAllC n (Semiformula.rel s w))
    (openAllC n (Semiformula.rel t u))
  have hr : (openAllC n (Semiformula.rel r v))ᴺ = ∼∼openAll n (Semiformulaᵢ.rel r v) := by
    rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hs : (openAllC n (Semiformula.rel s w))ᴺ = ∼∼openAll n (Semiformulaᵢ.rel s w) := by
    rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have ht : (openAllC n (Semiformula.rel t u))ᴺ = ∼∼openAll n (Semiformulaᵢ.rel t u) := by
    rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  rw [hr, hs, ht] at h
  obtain ⟨h⟩ := h
  obtain ⟨hnn⟩ := twoImp_dni (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (openAll n (Semiformulaᵢ.rel r v)) (openAll n (Semiformulaᵢ.rel s w))
    (openAll n (Semiformulaᵢ.rel t u))
  apply Nonempty.intro
  exact Entailment.cast (Entailment.C_trans hnn (Entailment.K_left h)) (by
    simp only [openAll_imp, openAll_gg, openAllC_imp])

theorem atomic_twoImp_closure {n k j l : ℕ} (r : language.Rel k) (s : language.Rel j)
    (t : language.Rel l) (v : Fin k → TermN n) (w : Fin j → TermN n) (u : Fin l → TermN n) :
    nativeTheory ⊢
      (∀⁰* ((Semiformulaᵢ.rel r v) 🡒 (Semiformulaᵢ.rel s w) 🡒 Semiformulaᵢ.rel t u)) 🡒
      (∀⁰* ((Semiformula.rel r v) 🡒 (Semiformula.rel s w) 🡒 Semiformula.rel t u))ᴺ := by
  have h := atomic_twoImp_image n r s t (fun i => Rew.emb (v i))
    (fun i => Rew.emb (w i)) (fun i => Rew.emb (u i))
  have hh := allClosure_imp n _ _ h
  obtain ⟨hh⟩ := hh
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [gg_allClosure, LogicalConnective.HomClass.map_imply, Rewriting.emb,
    Semiformula.rew_doubleNegation, Semiformulaᵢ.rew_rel, Function.comp_def] using hh
end DiophantineConsistency.IPRATwoImpLogic
