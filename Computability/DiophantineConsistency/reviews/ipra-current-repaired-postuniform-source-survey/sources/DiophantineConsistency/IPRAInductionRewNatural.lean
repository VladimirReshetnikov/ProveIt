import DiophantineConsistency.IPRAInductionFiniteMatrix
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRARewNatural
variable {L : Language} {ξ : Type} {n : ℕ}
theorem subst_q_natural (ω : Rew L ξ 0 ξ n) (t : Semiterm L ξ 0) :
    (Rew.subst (Fin.cases (ω t) (fun i => #i))).comp ω.q = ω.comp (Rew.subst ![t]) := by
  have hshift : (Rew.subst (Fin.cases (ω t) (fun i => #i))).comp Rew.bShift = Rew.id := by
    ext x <;> simp [Rew.comp_app]
  ext x
  · cases x using Fin.cases <;> simp [Rew.comp_app]
  · simp only [Rew.comp_app, Rew.q_fvar, Rew.subst_fvar]
    simpa only [Rew.comp_app, Rew.id_app] using Rew.ext' hshift (ω &x)
theorem subst_q_natural_lifted (ω : Rew L ξ 0 ξ n) (t : Semiterm L ξ 1) :
    (Rew.subst (Fin.cases (ω.q t) (fun i => #i.succ))).comp ω.q =
      ω.q.comp (Rew.subst ![t]) := by
  have hshift : (Rew.subst (Fin.cases (ω.q t) (fun i => #i.succ))).comp Rew.bShift = Rew.bShift := by
    ext x <;> simp [Rew.comp_app]
  ext x
  · cases x using Fin.cases <;> simp [Rew.comp_app]
  · simp only [Rew.comp_app, Rew.q_fvar, Rew.subst_fvar]
    simpa only [Rew.comp_app] using Rew.ext' hshift (ω &x)
theorem body_natural [L.ORing] (ω : Rew L ℕ 0 ℕ n) (p : Semiformulaᵢ L ℕ 1) :
    ω ▹ ((p/[‘0’]) 🡒 (∀⁰ ((p/[#0]) 🡒 (p/[‘(#0 + 1)’]))) 🡒 ∀⁰ (p/[#0])) =
    ((Rew.subst (Fin.cases (ω ‘0’) (fun i => #i)) ▹ (ω.q ▹ p)) 🡒
      (∀⁰ ((ω.q ▹ p) 🡒
        (Rew.subst (Fin.cases (ω.q ‘(#0 + 1)’) (fun i => #i.succ)) ▹ (ω.q ▹ p)))) 🡒
      ∀⁰ (ω.q ▹ p)) := by
  have hid : (Rew.subst ![#0] : Rew L ℕ 1 ℕ 1) = Rew.id := by
    ext x
    · cases x using Fin.cases <;> simp
    · simp
  simp only [LogicalConnective.HomClass.map_imply, Rewriting.app_all, Rewriting.subst, ← TransitiveRewriting.comp_app,
    subst_q_natural, subst_q_natural_lifted]
  simp only [hid, Rew.comp_id]
end DiophantineConsistency.IPRARewNatural
