import DiophantineConsistency.PRAUniversalSyntax
import Foundation.FirstOrder.Basic.CutFree

/-! Structural preparation for Herbrand extraction from cut-free proofs. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandExistentialSequents
open LO LO.FirstOrder
open scoped LO.FirstOrder

/-- No universal quantifier occurs anywhere in the formula. -/
def NoUniversal {L : Language} {ξ : Type} : {n : ℕ} → Semiformula L ξ n → Prop
  | _, .rel _ _ => True
  | _, .nrel _ _ => True
  | _, ⊤ => True
  | _, ⊥ => True
  | _, p ⋏ q => NoUniversal p ∧ NoUniversal q
  | _, p ⋎ q => NoUniversal p ∧ NoUniversal q
  | _, ∀⁰ _ => False
  | _, ∃⁰ p => NoUniversal p

theorem noUniversal_rew_iff {L : Language} {ξ η : Type} {n m : ℕ}
    (φ : Semiformula L ξ n) (w : Rew L ξ n η m) :
    NoUniversal (w ▹ φ) ↔ NoUniversal φ := by
  induction φ using Semiformula.rec' generalizing η m with
  | hverum => simp [NoUniversal]
  | hfalsum => simp [NoUniversal]
  | hrel r v => simp [NoUniversal]
  | hnrel r v => simp [NoUniversal]
  | hand p q ihp ihq => simp [NoUniversal, ihp, ihq]
  | hor p q ihp ihq => simp [NoUniversal, ihp, ihq]
  | hall p ih => simp [NoUniversal]
  | hexs p ih => simpa [NoUniversal] using ih w.q

theorem noUniversal_of_open {L : Language} {ξ : Type} {n : ℕ}
    (φ : Semiformula L ξ n) (h : φ.Open) : NoUniversal φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v => trivial
  | hnrel r v => trivial
  | hand p q ihp ihq =>
      simp only [Semiformula.Open, Semiformula.qr_and, Nat.max_eq_zero_iff] at h
      exact ⟨ihp h.1, ihq h.2⟩
  | hor p q ihp ihq =>
      simp only [Semiformula.Open, Semiformula.qr_or, Nat.max_eq_zero_iff] at h
      exact ⟨ihp h.1, ihq h.2⟩
  | hall p ih => simp [Semiformula.Open] at h
  | hexs p ih => simp [Semiformula.Open] at h

/-- No universal-rule node occurs anywhere in this derivation. -/
def NoAllRule {L : Language} : {Γ : Sequent L} → Derivation Γ → Prop
  | _, .identity _ _ => True
  | _, .verum => True
  | _, .cut d₁ d₂ => NoAllRule d₁ ∧ NoAllRule d₂
  | _, .contraction d _ => NoAllRule d
  | _, .or d => NoAllRule d
  | _, .and d₁ d₂ => NoAllRule d₁ ∧ NoAllRule d₂
  | _, .all _ => False
  | _, .exs d => NoAllRule d

/-- Traverse a concrete derivation and collect its existential-rule terms. -/
def existentialTerms {L : Language} : {Γ : Sequent L} → Derivation Γ → List (SyntacticTerm L)
  | _, .identity _ _ => []
  | _, .verum => []
  | _, .cut d₁ d₂ => existentialTerms d₁ ++ existentialTerms d₂
  | _, .contraction d _ => existentialTerms d
  | _, .or d => existentialTerms d
  | _, .and d₁ d₂ => existentialTerms d₁ ++ existentialTerms d₂
  | _, .all d => existentialTerms d
  | _, .exs (t := t) d => t :: existentialTerms d

/-- A cut-free proof whose end sequent has no universal quantifiers cannot
contain a universal-rule node. -/
theorem cutFree_noUniversalRule {L : Language} {Γ : Sequent L} (d : Derivation Γ)
    (hCutFree : d.IsCutFree) (hΓ : ∀ φ ∈ Γ, NoUniversal φ) : NoAllRule d := by
  induction d with
  | identity r v => trivial
  | verum => trivial
  | cut d₁ d₂ ih₁ ih₂ => exact False.elim (Derivation.IsCutFree.not_cut d₁ d₂ hCutFree)
  | contraction d ss ih =>
      apply ih (Derivation.isCutFree_contraction_iff.mp hCutFree)
      intro φ hφ
      exact hΓ φ (ss hφ)
  | @or p q Γ d ih =>
      have hpq : NoUniversal (p ⋎ q) := hΓ _ (by simp)
      apply ih (Derivation.isCutFree_or_iff.mp hCutFree)
      intro φ hφ
      simp only [List.mem_cons] at hφ
      rcases hφ with rfl | rfl | hφ
      · exact hpq.1
      · exact hpq.2
      · exact hΓ _ (by simp [hφ])
  | @and p Γ q d₁ d₂ ih₁ ih₂ =>
      have hpq : NoUniversal (p ⋏ q) := hΓ _ (by simp)
      have hc := Derivation.isCutFree_and_iff.mp hCutFree
      constructor
      · apply ih₁ hc.1
        intro φ hφ
        simp only [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · exact hpq.1
        · exact hΓ _ (by simp [hφ])
      · apply ih₂ hc.2
        intro φ hφ
        simp only [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · exact hpq.2
        · exact hΓ _ (by simp [hφ])
  | @all Γ p d ih =>
      have hp : NoUniversal (∀⁰ p) := hΓ _ (by simp)
      exact hp
  | @exs p t Γ d ih =>
      apply ih (Derivation.isCutFree_exs_iff.mp hCutFree)
      intro φ hφ
      simp only [List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · have hp' : NoUniversal (∃⁰ p) := hΓ _ (by simp)
        have hp : NoUniversal p := hp'
        exact (noUniversal_rew_iff p (Rew.subst (fun _ => t))).mpr hp
      · exact hΓ _ (by simp [hφ])

end DiophantineConsistency.HerbrandExistentialSequents
