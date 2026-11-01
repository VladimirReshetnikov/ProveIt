import DiophantineConsistency.ParsonsOpened
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBlock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsOpened
variable {L : Language} [L.ORing]

omit [L.ORing] in
theorem closure_outer {n : ℕ} (A : Semiformula L ℕ (1 + n)) :
    (∃⁰* A) = ∃⁰ (∃⁰^[n] A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [exsClosure_succ, exsItr_succ]
    exact ih (∃⁰ A)

omit [L.ORing] in
theorem itr_closure {n : ℕ} (A : Semiformula L ℕ (0 + n)) :
    (∃⁰^[n] A) = ∃⁰* A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [exsClosure_succ, exsItr_succ]
    exact ih (∃⁰ A)

/-- A partially instantiated parameter body. The remaining `n` bound variables
are precisely the parameters still hidden by the outer existential block. -/
def State (φ : Semiproposition L 1) {n : ℕ} (A : Semiformula L ℕ n) : Prop :=
  ∃ v : Fin (0 + (succInd φ).fvSup) → Semiterm L ℕ n,
    A = (normalizedBody φ) ⇜ v

theorem start (φ : Semiproposition L 1) : State φ (normalizedBody φ) := by
  exact ⟨fun i => #i, by simp [Rewriting.subst]⟩

def advance {n : ℕ} (A : Semiformula L ℕ (1 + n)) (t : SyntacticTerm L) :
    Semiformula L ℕ (0 + n) := (Rew.subst ![t]).qpow n ▹ A

omit [L.ORing] in
theorem opening {n : ℕ} (A : Semiformula L ℕ (1 + n)) (t : SyntacticTerm L) :
    ((∃⁰^[n] A)/[t]) = ∃⁰* advance A t := by
  simp [advance, Rewriting.subst, itr_closure]

omit [L.ORing] in
theorem qpow_subst_fvar (t : SyntacticTerm L) (n x : ℕ) :
    ((Rew.subst ![t]).qpow n) (&x) = &x := by
  induction n with
  | zero => simp
  | succ n ih => simp [Rew.qpow_succ, ih]

theorem step {n : ℕ} (φ : Semiproposition L 1) (A : Semiformula L ℕ (1 + n))
    (t : SyntacticTerm L) (h : State φ A) : State φ (advance A t) := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨fun i => (Rew.subst ![t]).qpow n (v i), ?_⟩
  simp only [advance, Rewriting.subst, ← TransitiveRewriting.comp_app]
  apply congrArg (fun ω : SyntacticRew L (0 + (succInd φ).fvSup) (0 + n) => ω ▹ normalizedBody φ)
  ext i
  · simp [Rew.comp_app]
  · simp [Rew.comp_app, qpow_subst_fvar]

/-- After all parameter quantifiers have been opened, the resulting formula
is the existing principal existential matrix for some vector of terms. -/
theorem finish (φ : Semiproposition L 1) (A : Proposition L) (h : State φ A) :
    ∃ f : ℕ → SyntacticTerm L,
      A = ∃⁰ ParsonsInductionCase.matrix ((Rew.rewrite f).q ▹ φ) := by
  obtain ⟨v, rfl⟩ := h
  let f : ℕ → SyntacticTerm L := fun x => if h : x < (0 + (succInd φ).fvSup) then v ⟨x,h⟩ else &x
  refine ⟨f, ?_⟩
  have hv : (fun x : Fin (0 + (succInd φ).fvSup) => f ↑x) = v := by
    funext x
    have hx : (x : ℕ) < (succInd φ).fvSup := by simpa using x.isLt
    simp [f, hx]
  rw [← hv]
  exact normalized_instance φ f

/-- Principal existential parameter case of the cut-free recursion. The
recursive hypothesis is invoked on the actual rewritten premise, whose height
is strictly below this very existential inference. -/
theorem principal_parameter {n : ℕ} {T : Theory L} (φ : Semiproposition L 1)
    (A : Semiformula L ℕ (1 + n)) (t : SyntacticTerm L) (Γ : Sequent L)
    (E : Proposition L) (d : Derivation (((∃⁰^[n] A)/[t]) :: Γ))
    (hc : Derivation.IsCutFree d) (hs : State φ A)
    (ih : ∀ e : Derivation ((∃⁰* advance A t) :: Γ),
      Derivation.IsCutFree e → e.height < d.exs.height → State φ (advance A t) →
      Nonempty (ParsonsRule.Proof T E)) : Nonempty (ParsonsRule.Proof T E) := by
  have heq : ((∃⁰^[n] A)/[t]) :: Γ = (∃⁰* advance A t) :: Γ := by
    rw [opening]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height = d.height := by simp [e]
  apply ih e he
  · simp only [Derivation.height_exs]; omega
  · exact step φ A t hs

end DiophantineConsistency.ParsonsBlock
