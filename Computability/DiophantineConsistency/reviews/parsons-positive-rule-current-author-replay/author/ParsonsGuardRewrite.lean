import DiophantineConsistency.ParsonsGuardPrefix
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardRewrite
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardPrefix

theorem rewrite {P : Proposition ℒₒᵣ} (h : Guard P) (f : ℕ → SyntacticTerm ℒₒᵣ) :
    Guard (Rew.rewrite f ▹ P) := by
  induction h generalizing f with
  | sigma h => exact .sigma (Hierarchy.rew _ h)
  | all A hA h ih =>
      have hi := ih (&0 :>ₙ fun x => Rew.shift (f x))
      have hp : Hierarchy 𝚷 2 (∀⁰ ((Rew.rewrite f).q ▹ A)) := by
        simpa using Hierarchy.rew (Rew.rewrite f) hA
      have hb : Guard (((Rew.rewrite f).q ▹ A).free) := by
        have heq : (((Rew.rewrite f).q ▹ A).free) =
            Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) ▹ A.free := by
          simpa only [Rew.q_rewrite, Function.comp_def] using
            (LawfulSyntacticRewriting.free_rewrite_eq f A)
        rw [heq]
        exact hi
      simpa using Guard.all ((Rew.rewrite f).q ▹ A) hp hb

/-- A universal whose body is Σ₁ is an explicit guarded prefix. -/
theorem all_sigma (A : ArithmeticSemiformula ℕ 1) (hA : Hierarchy 𝚺 1 A) :
    Guard (∀⁰ A) :=
  Guard.all A (Hierarchy.all (hA.strict_mono 𝚷 (s' := 2) (by decide)))
    (Guard.sigma (Hierarchy.rew Rew.free hA))
end DiophantineConsistency.ParsonsGuardRewrite
