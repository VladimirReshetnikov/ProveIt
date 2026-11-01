import DiophantineConsistency.ParsonsInductionCase
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsParameters
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule
variable {L : Language} [L.ORing]

theorem neg_ind (φ : Semiproposition L 1) :
    ∼(succInd φ) = base φ ⋏ (step φ ⋏ (∃⁰ (∼φ))) := by
  simp [succInd, base, step, Semiformula.imp_eq]

def parameterBody (φ : Semiproposition L 1) :
    Semiformula L ℕ (0 + (succInd φ).fvSup) :=
  Rew.fixitr 0 (succInd φ).fvSup ▹ (base φ ⋏ (step φ ⋏ (∃⁰ (∼φ))))

theorem neg_closed_ind (φ : Semiproposition L 1) :
    ∼((succInd φ).univCl : Proposition L) = ∃⁰* (parameterBody φ) := by
  simp [Semiformula.univCl', parameterBody, ← neg_ind]

theorem parameterBody_subst (φ : Semiproposition L 1) :
    (parameterBody φ) ⇜ (fun x ↦ (&↑x : SyntacticTerm L)) = ∼(succInd φ) := by
  simp [parameterBody, ← neg_ind]

/-- Restoring any terms for the closed parameters yields the same terms
    substituted for the free parameters in the original counterexample. -/
theorem parameterBody_subst_terms (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    (parameterBody φ) ⇜ (fun x ↦ f ↑x) = Rew.rewrite f ▹ ∼(succInd φ) := by
  simp [parameterBody, ← neg_ind]

theorem rewrite_ind (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    Rew.rewrite f ▹ succInd φ = succInd ((Rew.rewrite f).q ▹ φ) := by
  have h0 : (Rew.rewrite f).comp (Rew.subst ![(‘0’ : SyntacticTerm L)]) =
      (Rew.subst ![(‘0’ : SyntacticTerm L)]).comp (Rew.rewrite f).q := by
    ext i <;> simp [Rew.comp_app]
  have hb : (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]).comp
      (@Rew.bShift L ℕ 0) = @Rew.bShift L ℕ 0 := by
    ext i
    · exact Fin.elim0 i
    · simp [Rew.comp_app]
  have hi : (Rew.subst ![(#0 : Semiterm L ℕ 1)]) = Rew.id := by
    ext i <;> simp
  have hs : (Rew.rewrite f).q.comp (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]) =
      (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]).comp (Rew.rewrite f).q := by
    ext i
    · simp [Rew.comp_app]
    · change Rew.bShift (f i) = (Rew.subst ![(‘(#0 + 1)’ : Semiterm L ℕ 1)]) (Rew.bShift (f i))
      exact (Rew.ext' hb (f i)).symm
  simp [succInd, ← TransitiveRewriting.comp_app, h0, hs, hi]

/-- Opening all closed parameters by arbitrary terms recovers an actual
    negated induction formula whose matrix uses the rewritten parameters. -/
theorem parameterBody_instance (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    (parameterBody φ) ⇜ (fun x ↦ f ↑x) =
      ∼(succInd ((Rew.rewrite f).q ▹ φ)) := by
  simp [parameterBody_subst_terms, rewrite_ind]

theorem parameter_instance_sigma (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L)
    (h : Hierarchy 𝚺 1 φ) : Hierarchy 𝚺 1 ((Rew.rewrite f).q ▹ φ) :=
  Hierarchy.rew _ h

/-- Explicit LK normalization once all parameter terms have been fixed. -/
def instance_normalization (φ : Semiproposition L 1) (f : ℕ → SyntacticTerm L) :
    Derivation [∼((parameterBody φ) ⇜ (fun x ↦ f ↑x)),
      ∃⁰ (ParsonsInductionCase.matrix ((Rew.rewrite f).q ▹ φ))] := by
  simpa [parameterBody_instance] using
    ParsonsInductionCase.induction_normalization ((Rew.rewrite f).q ▹ φ)

end DiophantineConsistency.ParsonsParameters
