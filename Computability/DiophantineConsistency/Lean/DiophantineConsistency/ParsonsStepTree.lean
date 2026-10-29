import DiophantineConsistency.ParsonsGuardTree
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStepTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardTree ParsonsRule

/-- For bounded induction predicates, the actual step side is a guard tree. -/
theorem bounded (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 0 φ) : Tree (step φ) := by
  have hs : Hierarchy 𝚺 1 φ := hφ.mono (by decide)
  have hp : Hierarchy 𝚷 2 (step φ) := ParsonsSide.step_pi_two φ hs
  have hb : Hierarchy 𝚺 1 (stepBody φ) := by
    have hzero : Hierarchy 𝚺 0 (stepBody φ) := by
      simpa [stepBody, Semiformula.imp_eq] using And.intro (Hierarchy.zero_eq_alt hφ) hφ
    exact hzero.mono (by decide)
  rw [step_def] at hp ⊢
  exact Tree.all (stepBody φ) hp (Tree.sigma (Hierarchy.rew Rew.free hb))

/-- The negation of an existential with bounded matrix is one universal
followed by a Σ₁ leaf. -/
theorem neg_bounded_exists (D : ArithmeticSemiformula ℕ 1) (hD : Hierarchy 𝚺 0 D) :
    Tree (∼(∃⁰ D)) := by
  have hd : Hierarchy 𝚺 1 (∼D) := (Hierarchy.neg hD).accum 𝚺
  have hp : Hierarchy 𝚷 2 (∀⁰ (∼D)) := Hierarchy.all (hd.strict_mono 𝚷 (s' := 2) (by decide))
  simpa using Tree.all (∼D) hp (Tree.sigma (Hierarchy.rew Rew.free hd))

/-- A strict Σ₁ induction predicate has a tree descriptor for the actual
step side; no normalization or source proof transformation is assumed. -/
theorem strict (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D) :
    Tree (step (∃⁰ D)) := by
  let φ : ArithmeticSemiformula ℕ 1 := ∃⁰ D
  have hφ : Hierarchy 𝚺 1 φ := by
    apply Hierarchy.exs
    exact hD.mono (by decide)
  have hp : Hierarchy 𝚷 2 (step φ) := ParsonsSide.step_pi_two φ hφ
  have hn : Tree (∼φ.free) := by
    let D' : ArithmeticSemiformula ℕ 1 := (Rew.free).q ▹ D
    have hD' : Hierarchy 𝚺 0 D' := Hierarchy.rew _ hD
    have hh := neg_bounded_exists D' hD'
    simpa [φ, D'] using hh
  have hs : Hierarchy 𝚺 1 (succBody φ).free := by
    have hS : Hierarchy 𝚺 1 (succBody φ) := by simpa [succBody] using hφ
    exact Hierarchy.rew Rew.free hS
  have hbody : Tree (stepBody φ).free := by
    have heq : (stepBody φ).free = ∼φ.free ⋎ (succBody φ).free := by
      simp [stepBody, succBody, Semiformula.imp_eq]
    rw [heq]
    exact Tree.or hn (Tree.sigma hs)
  rw [step_def] at hp ⊢
  exact Tree.all (stepBody φ) hp hbody

/-- The negative counterexample side for the same strict predicate is also a
universal bounded guard, at any witness term. -/
theorem strict_negative (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D)
    (t : SyntacticTerm ℒₒᵣ) : Tree (∼((∃⁰ D)/[t])) := by
  let D' : ArithmeticSemiformula ℕ 1 := (Rew.subst ![t]).q ▹ D
  have hD' : Hierarchy 𝚺 0 D' := Hierarchy.rew _ hD
  have hh := neg_bounded_exists D' hD'
  simpa [D'] using hh
end DiophantineConsistency.ParsonsStepTree
