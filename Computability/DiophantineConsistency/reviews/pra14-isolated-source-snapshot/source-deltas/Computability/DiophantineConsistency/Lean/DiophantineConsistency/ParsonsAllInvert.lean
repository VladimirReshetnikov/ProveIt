import DiophantineConsistency.ParsonsLeaves
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsAllInvert
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

set_option backward.isDefEq.respectTransparency false in
theorem height_rewrite {L : Language} {Γ : Sequent L} (d : Derivation Γ)
    (f : ℕ → SyntacticTerm L) : (d.rewrite f).height = d.height := by
  induction d generalizing f <;> simp [Derivation.rewrite, Derivation.height, *]

inductive Selection {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L) :
    Sequent L → Sequent L → Prop
  | nil : Selection A t [] []
  | keep {Γ Δ} (φ : Proposition L) : Selection A t Γ Δ → Selection A t (φ :: Γ) (φ :: Δ)
  | replace {Γ Δ} : Selection A t Γ Δ → Selection A t ((∀⁰ A) :: Γ) ((A/[t]) :: Δ)

theorem choice {L : Language} {A : Semiproposition L 1} {t : SyntacticTerm L} {Γ Δ : Sequent L}
    (h : Selection A t Γ Δ) {φ : Proposition L} (hφ : φ ∈ Γ) :
    φ ∈ Δ ∨ (φ = ∀⁰ A ∧ A/[t] ∈ Δ) := by
  induction h with
  | nil => simp at hφ
  | keep ψ h ih =>
      rcases List.mem_cons.mp hφ with rfl | ht
      · exact Or.inl (by simp)
      · rcases ih ht with hl | ⟨eq, ha⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha]⟩
  | replace h ih =>
      rcases List.mem_cons.mp hφ with he | ht
      · exact Or.inr ⟨he, by simp⟩
      · rcases ih ht with hl | ⟨eq, ha⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha]⟩

theorem pullback {L : Language} {A : Semiproposition L 1} {t : SyntacticTerm L} {Γ Δ Ξ : Sequent L}
    (h : Selection A t Γ Δ) (sub : Ξ ⊆ Γ) :
    ∃ Ω, Selection A t Ξ Ω ∧ Ω ⊆ Δ := by
  induction Ξ with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons φ Ξ ih =>
      have hφ : φ ∈ Γ := sub (by simp)
      obtain ⟨Ω, hs, hsub⟩ := ih (fun ψ hp => sub (by simp [hp]))
      rcases choice h hφ with hp | ⟨he, hp⟩
      · exact ⟨φ :: Ω, .keep φ hs, by simpa using ⟨hp,hsub⟩⟩
      · subst φ
        exact ⟨A/[t] :: Ω, .replace hs, by simpa using ⟨hp,hsub⟩⟩

theorem shift {L : Language} {A : Semiproposition L 1} {t : SyntacticTerm L} {Γ Δ : Sequent L}
    (h : Selection A t Γ Δ) :
    Selection (Rew.shift ▹ A) (Rew.shift t) Γ⁺ Δ⁺ := by
  induction h with
  | nil => simp [Rewriting.shifts, Selection.nil]
  | keep φ h ih => simpa [Rewriting.shifts] using Selection.keep (Rewriting.shift φ) ih
  | replace h ih =>
      have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm L)) = (@Rew.shift L 0) := by
        ext i <;> simp
      have he : Rewriting.shift (A/[t]) = (Rew.shift ▹ A)/[Rew.shift t] := by
        simpa [hr, ← Rew.q_rewrite] using
          (LawfulSyntacticRewriting.rewrite_subst_eq (fun x : ℕ => (&(x+1) : SyntacticTerm L)) t A)
      simpa [Rewriting.shifts, he] using Selection.replace ih

theorem same {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L) (Γ : Sequent L) :
    Selection A t Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons φ Γ ih => exact .keep φ ih

/-- The eigenvariable premise instantiated at an arbitrary witness; rewriting
preserves cut-freeness and height. -/
def instantiate_premise {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) (d : Derivation (A.free :: Γ⁺)) : Derivation (A/[t] :: Γ) := by
  let f : ℕ → SyntacticTerm L := t :>ₙ (fun x => &x)
  have heq : (A.free :: Γ⁺).map (Rew.rewrite f ▹ ·) = A/[t] :: Γ := by
    dsimp only [f, List.map_cons]
    rw [LawfulSyntacticRewriting.rewrite_free_eq_subst]
    simp [Rewriting.shifts, List.map_map, Function.comp_def, ← TransitiveRewriting.comp_app,
      Rew.rewrite_comp_shift_eq_id]
  exact (d.rewrite f).cast heq

theorem instantiate_height {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) (d : Derivation (A.free :: Γ⁺)) :
    (instantiate_premise A t Γ d).height = d.height := by
  simp only [instantiate_premise, Derivation.height_cast]
  exact height_rewrite d _

theorem instantiate_cutFree {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) (d : Derivation (A.free :: Γ⁺)) (hc : Derivation.IsCutFree d) :
    Derivation.IsCutFree (instantiate_premise A t Γ d) := by
  simp only [instantiate_premise, Derivation.IsCutFree.cast,
    Derivation.isCutFree_rewrite_iff_isCutFree]
  exact hc

theorem invert_aux {L : Language} (m : ℕ) :
    ∀ {Γ : Sequent L} (d : Derivation Γ), d.height < m → Derivation.IsCutFree d →
      ∀ (A : Semiproposition L 1) (t : SyntacticTerm L) {Δ : Sequent L}, Selection A t Γ Δ →
      ∃ e : Derivation Δ, Derivation.IsCutFree e ∧ e.height ≤ d.height := by
  induction m with
  | zero => intro Γ d hd; omega
  | succ m ih =>
    intro Γ d hd hc A t Δ hs
    cases hc with
    | identity r v =>
        cases hs with
        | keep _ h =>
            cases h with
            | keep _ h =>
                cases h
                exact ⟨Derivation.identity r v, .identity r v, le_rfl⟩
    | verum =>
        cases hs with
        | keep _ h =>
            cases h
            exact ⟨Derivation.verum, .verum, le_rfl⟩
    | or hc =>
        cases hs with
        | keep _ hs =>
            obtain ⟨e, he, hb⟩ := ih _ (by simp only [Derivation.height_or] at hd; omega)
              hc A t (.keep _ (.keep _ hs))
            exact ⟨e.or, .or he, by simp only [Derivation.height_or]; omega⟩
    | and hca hcb =>
        cases hs with
        | keep _ hs =>
            obtain ⟨ea, hfa, ha⟩ := ih _ (by simp only [Derivation.height_and] at hd; omega)
              hca A t (.keep _ hs)
            obtain ⟨eb, hfb, hb⟩ := ih _ (by simp only [Derivation.height_and] at hd; omega)
              hcb A t (.keep _ hs)
            refine ⟨ea.and eb, .and hfa hfb, ?_⟩
            simp only [Derivation.height_and]; omega
    | @all B Θ d0 hc =>
        cases hs with
        | keep _ hs =>
            obtain ⟨e, he, hb⟩ := ih d0 (by simp only [Derivation.height_all] at hd; omega)
              hc (Rew.shift ▹ A) (Rew.shift t) (.keep _ (shift hs))
            exact ⟨e.all, .all he, by simp only [Derivation.height_all]; omega⟩
        | replace hs =>
            let d' := instantiate_premise A t Θ d0
            have hfree : Derivation.IsCutFree d' := instantiate_cutFree A t Θ d0 hc
            have hh : d'.height = d0.height := instantiate_height A t Θ d0
            obtain ⟨e, he, hb⟩ := ih d' (by simp only [Derivation.height_all] at hd; omega)
              hfree A t (.keep _ hs)
            exact ⟨e, he, by simp only [Derivation.height_all]; omega⟩
    | exs u hc =>
        cases hs with
        | keep _ hs =>
            obtain ⟨e, he, hb⟩ := ih _ (by simp only [Derivation.height_exs] at hd; omega)
              hc A t (.keep _ hs)
            exact ⟨e.exs, .exs u he, by simp only [Derivation.height_exs]; omega⟩
    | contraction ss hc =>
        obtain ⟨Ω, hs', hsub⟩ := pullback hs ss
        obtain ⟨e, he, hb⟩ := ih _ (by simp only [Derivation.height_contraction] at hd; omega)
          hc A t hs'
        exact ⟨e.contraction hsub, .contraction hsub he,
          by simp only [Derivation.height_contraction]; omega⟩

theorem invert {L : Language} {Γ : Sequent L} (d : Derivation Γ)
    (hc : Derivation.IsCutFree d) (A : Semiproposition L 1) (t : SyntacticTerm L)
    {Δ : Sequent L} (hs : Selection A t Γ Δ) :
    ∃ e : Derivation Δ, Derivation.IsCutFree e ∧ e.height ≤ d.height :=
  invert_aux (d.height + 1) d (by omega) hc A t hs

/-- Invert the first universal formula of a cut-free sequent. -/
theorem invert_first {L : Language} (A : Semiproposition L 1)
    (t : SyntacticTerm L) (Γ : Sequent L) (d : Derivation ((∀⁰ A) :: Γ))
    (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (A/[t] :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height :=
  invert d hc A t (.replace (same A t Γ))

/-- Opening a side universal in an existential-rule premise stays strictly
below the height of the original existential conclusion. -/
theorem invert_below_exs {L : Language} (A B : Semiproposition L 1)
    (t u : SyntacticTerm L) (Γ : Sequent L)
    (d : Derivation (B/[u] :: (∀⁰ A) :: Γ)) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (B/[u] :: A/[t] :: Γ),
      Derivation.IsCutFree e ∧ e.height < d.exs.height := by
  obtain ⟨e, he, hb⟩ := invert d hc A t (.keep _ (.replace (same A t Γ)))
  exact ⟨e, he, by simp only [Derivation.height_exs]; omega⟩

end DiophantineConsistency.ParsonsAllInvert
