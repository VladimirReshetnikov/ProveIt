import DiophantineConsistency.ParsonsClosure
import DiophantineConsistency.ParsonsParameters
import DiophantineConsistency.ParsonsTheoryNormalize
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsOpened
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsClosure ParsonsInductionCase ParsonsParameters
variable {L : Language} [L.ORing]

omit [L.ORing] in
theorem bShift_fvar {n : ℕ} (ψ : Semiformula L ℕ n) (x : ℕ)
    (h : (Rew.bShift ▹ ψ).FVar? x) : ψ.FVar? x := by
  rcases Semiformula.fvar?_rew h with ⟨i, hi⟩ | ⟨z, hz, hi⟩
  · simp at hi
  · simp at hi; subst x; exact hz

theorem counterexample_support (φ : Semiproposition L 1) (x : ℕ)
    (h : (∃⁰ matrix φ).FVar? x) : (succInd φ).FVar? x := by
  simp [matrix, Semiformula.FVar?] at h
  simp [succInd, Semiformula.imp_eq, Semiformula.FVar?]
  rcases h with h | h | h
  · left; simpa [base, Semiformula.FVar?] using bShift_fvar (base φ) x h
  · right; have hs := bShift_fvar (step φ) x h
    simp [step, Semiformula.imp_eq, Semiformula.FVar?] at hs
    tauto
  · exact Or.inr (Or.inl h)

theorem counterexample_open (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    (Rew.fixitr 0 (succInd φ).fvSup ▹ (∃⁰ matrix φ)) ⇜ (fun x ↦ f ↑x) =
      Rew.rewrite f ▹ (∃⁰ matrix φ) := by
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  apply Semiformula.rew_eq_of_funEqOn
  · simp
  · intro x hx
    have hx' : x < (succInd φ).fvSup :=
      Semiformula.lt_fvSup_of_fvar? (counterexample_support φ x hx)
    simp [Rew.comp_app, Rew.fixitr_fvar, hx']

theorem rewrite_counterexample (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    Rew.rewrite f ▹ (∃⁰ matrix φ) = ∃⁰ matrix ((Rew.rewrite f).q ▹ φ) := by
  have hi : (Rew.subst ![(#0 : Semiterm L ℕ 1)]) = Rew.id := by
    ext i <;> simp
  have hb : (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]).comp
      (@Rew.bShift L ℕ 0) = @Rew.bShift L ℕ 0 := by
    ext i
    · exact Fin.elim0 i
    · simp [Rew.comp_app]
  simp [matrix, base, step, ← TransitiveRewriting.comp_app]
  constructor
  · congr 2
    ext i <;> simp [Rew.comp_app]
  constructor
  · congr 2
    ext i <;> simp [Rew.comp_app, hi]
  · congr 2
    ext i
    · simp [Rew.comp_app]
    · simp only [Rew.comp_app, Rew.q_fvar, Rew.rewrite_fvar]
      have he : (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]) (Rew.bShift (f i)) =
          Rew.bShift (f i) := Rew.ext' hb (f i)
      rw [he]
      simp

/-- The exact body in the normalized proof, with one binder per original
    free-parameter index. -/
def normalizedBody (φ : Semiproposition L 1) :
    Semiformula L ℕ (0 + (succInd φ).fvSup) :=
  Rew.fixitr 0 (succInd φ).fvSup ▹ (∃⁰ matrix φ)

theorem normalized_shape (φ : Semiproposition L 1) :
    normalizedCounterexample φ = ∃⁰* normalizedBody φ := rfl

/-- Simultaneously opening the entire parameter block gives exactly the
    principal existential formula used by `one_case`. -/
theorem normalized_instance (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    (normalizedBody φ) ⇜ (fun x ↦ f ↑x) =
      ∃⁰ matrix ((Rew.rewrite f).q ▹ φ) := by
  exact (counterexample_open φ f).trans (rewrite_counterexample φ f)

/-- Principal counter-witness case for any induction formula selected from an
    actual normalized IΣ₁ proof. The three smaller recursive cases remain
    explicit hypotheses; no global translation is assumed. -/
theorem selected_principal {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (φ : ArithmeticSemiformula ℕ 1) (hmem : φ ∈ p.formulas)
    (f : ℕ → SyntacticTerm ℒₒᵣ) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) (Γ : Sequent ℒₒᵣ)
    (d : Derivation ((matrix ((Rew.rewrite f).q ▹ φ))/[t] :: Γ))
    (hc : Derivation.IsCutFree d) (hE : Hierarchy 𝚺 1 E)
    (hbase : ∀ e : Derivation (base ((Rew.rewrite f).q ▹ φ) :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (ParsonsRule.Proof 𝗣𝗔⁻ (base ((Rew.rewrite f).q ▹ φ) ⋎ E)))
    (hstep : ∀ e : Derivation (step ((Rew.rewrite f).q ▹ φ) :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (ParsonsRule.Proof 𝗣𝗔⁻ (step ((Rew.rewrite f).q ▹ φ) ⋎ E)))
    (hneg : ∀ e : Derivation (∼(((Rew.rewrite f).q ▹ φ)/[t]) :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (ParsonsRule.Proof 𝗣𝗔⁻ (∼(((Rew.rewrite f).q ▹ φ)/[t]) ⋎ E))) :
    Nonempty (ParsonsRule.Proof 𝗣𝗔⁻ E) :=
  one_case ((Rew.rewrite f).q ▹ φ) E t Γ d hc (Hierarchy.rew _ (p.formulas_mem φ hmem))
    hE hbase hstep hneg

end DiophantineConsistency.ParsonsOpened
