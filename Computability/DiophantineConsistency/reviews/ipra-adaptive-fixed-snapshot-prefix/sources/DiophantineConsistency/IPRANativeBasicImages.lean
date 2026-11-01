import DiophantineConsistency.IPRANativeEquationImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeBasicImages
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree
open IPRANativeTheory IPRANativeAxiomImage IPRANativeEquationImages
variable {L : Language} {Λ : Hilbertᵢ L}

theorem allClosure_imp (n : ℕ) (φ ψ : Semipropositionᵢ L n)
    (h : Λ ⊢ openAll n φ 🡒 openAll n ψ) :
    Λ ⊢ (∀⁰* φ) 🡒 (∀⁰* ψ) := by
  have hh := allClosure_fixitr_imp h n
  have hi := congrArg (fun x : Semipropositionᵢ L n => ∀⁰* x) (openAll_inverse n φ)
  have hj := congrArg (fun x : Semipropositionᵢ L n => ∀⁰* x) (openAll_inverse n ψ)
  have hc1 := allClosure_cast (Nat.zero_add n) (Rew.fixitr 0 n ▹ openAll n φ)
  have hc2 := allClosure_cast (Nat.zero_add n) (Rew.fixitr 0 n ▹ openAll n ψ)
  have hi' : (∀⁰* (Rew.fixitr 0 n ▹ openAll n φ)) = ∀⁰* φ := hc1.symm.trans hi
  have hj' : (∀⁰* (Rew.fixitr 0 n ▹ openAll n ψ)) = ∀⁰* ψ := hc2.symm.trans hj
  simpa only [hi', hj'] using hh

theorem openAll_imp (n : ℕ) (φ ψ : Semipropositionᵢ L n) :
    openAll n (φ 🡒 ψ) = (openAll n φ 🡒 openAll n ψ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [openAll, LogicalConnective.HomClass.map_imply, ih]

def openAllC : (n : ℕ) → Semiproposition L n → Proposition L
  | 0, φ => φ
  | n+1, φ => openAllC n (Rewriting.free φ)

theorem openAllC_imp (n : ℕ) (φ ψ : Semiproposition L n) :
    openAllC n (φ 🡒 ψ) = (openAllC n φ 🡒 openAllC n ψ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [openAllC, LogicalConnective.HomClass.map_imply, ih]

theorem openAll_gg (n : ℕ) (φ : Semiproposition L n) :
    openAll n φᴺ = (openAllC n φ)ᴺ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [openAll, openAllC, Rewriting.free, Semiformula.rew_doubleNegation] using
      ih (Rewriting.free φ)

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem atomic_imp_image (n : ℕ) {k j : ℕ} (r : language.Rel k) (s : language.Rel j)
    (v : Fin k → Semiterm language ℕ n) (w : Fin j → Semiterm language ℕ n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      openAll n ((Semiformulaᵢ.rel r v) 🡒 Semiformulaᵢ.rel s w) 🡒
      openAll n (((Semiformula.rel r v) 🡒 Semiformula.rel s w)ᴺ) := by
  have h := Derivation.imply_doubleNegation (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (openAllC n (Semiformula.rel r v)) (openAllC n (Semiformula.rel s w))
  have hr : (openAllC n (Semiformula.rel r v))ᴺ =
      ∼∼openAll n (Semiformulaᵢ.rel r v) := by
    rw [←openAll_gg]
    simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hs : (openAllC n (Semiformula.rel s w))ᴺ =
      ∼∼openAll n (Semiformulaᵢ.rel s w) := by
    rw [←openAll_gg]
    simp only [Semiformula.doubleNegation_rel, openAll_neg]
  rw [hr, hs] at h
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  have h' := Entailment.C_trans Entailment.CCCNNNN (Entailment.K_left h)
  exact Entailment.cast h' (by simp only [openAll_imp, openAll_gg, openAllC_imp])
theorem atomic_imp_closure {n k j : ℕ} (r : language.Rel k) (s : language.Rel j)
    (v : Fin k → TermN n) (w : Fin j → TermN n) : nativeTheory ⊢
      (∀⁰* ((Semiformulaᵢ.rel r v) 🡒 Semiformulaᵢ.rel s w)) 🡒
      (∀⁰* ((Semiformula.rel r v) 🡒 Semiformula.rel s w))ᴺ := by
  have h := atomic_imp_image n r s (fun i => Rew.emb (v i))
    (fun i => Rew.emb (w i))
  have hh := allClosure_imp n _ _ h
  obtain ⟨hh⟩ := hh
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [gg_allClosure, LogicalConnective.HomClass.map_imply, Rewriting.emb, Semiformula.rew_doubleNegation, Semiformulaᵢ.rew_rel, Function.comp_def] using hh

theorem succInjective_image : nativeTheory ⊢ succInjectiveᴺ := by
  have ha : nativeTheory ⊢ succInjectiveI :=
    native_axiom (NativeAxiom.basic BasicAxiomI.succInjective)
  apply mdp! (atomic_imp_closure Language.ORing.Rel.eq Language.ORing.Rel.eq _ _)
  simpa only [succInjectiveI] using ha
theorem openAll_and (n : ℕ) (φ ψ : Semipropositionᵢ L n) :
    openAll n (φ ⋏ ψ) = (openAll n φ ⋏ openAll n ψ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [openAll, LogicalConnective.HomClass.map_and, ih]

theorem atomic_iff_image (n : ℕ) {k j : ℕ} (r : language.Rel k) (s : language.Rel j)
    (v : Fin k → Semiterm language ℕ n) (w : Fin j → Semiterm language ℕ n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      openAll n ((Semiformulaᵢ.rel r v) 🡘 Semiformulaᵢ.rel s w) 🡒
      openAll n (((Semiformula.rel r v) 🡘 Semiformula.rel s w)ᴺ) := by
  have h₁ := atomic_imp_image n r s v w
  have h₂ := atomic_imp_image n s r w v
  have h := Entailment.CKK!_of_C!_of_C! h₁ h₂
  simpa only [LogicalConnective.iff, Semiformula.doubleNegation_and, openAll_and] using h

theorem atomic_iff_closure {n k j : ℕ} (r : language.Rel k) (s : language.Rel j)
    (v : Fin k → TermN n) (w : Fin j → TermN n) : nativeTheory ⊢
      (∀⁰* ((Semiformulaᵢ.rel r v) 🡘 Semiformulaᵢ.rel s w)) 🡒
      (∀⁰* ((Semiformula.rel r v) 🡘 Semiformula.rel s w))ᴺ := by
  have h := atomic_iff_image n r s (fun i => Rew.emb (v i))
    (fun i => Rew.emb (w i))
  have hh := allClosure_imp n _ _ h
  obtain ⟨hh⟩ := hh
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [gg_allClosure, LogicalConnective.HomClass.map_iff, Rewriting.emb,
    Semiformula.rew_doubleNegation, Semiformulaᵢ.rew_rel, Function.comp_def] using hh

theorem orderDefinition_image : nativeTheory ⊢ orderDefinitionᴺ := by
  have ha : nativeTheory ⊢ orderDefinitionI :=
    native_axiom (NativeAxiom.basic BasicAxiomI.orderDefinition)
  apply mdp! (atomic_iff_closure Language.ORing.Rel.lt Language.ORing.Rel.eq _ _)
  simpa only [orderDefinitionI] using ha
theorem basicAxiom_image {σ : Sentence language} (h : BasicAxiom σ) : nativeTheory ⊢ σᴺ := by
  cases h with
  | succNonzero => exact succNonzero_image
  | succInjective => exact succInjective_image
  | orderDefinition => exact orderDefinition_image
end DiophantineConsistency.IPRANativeBasicImages
