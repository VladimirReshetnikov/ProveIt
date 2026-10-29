import DiophantineConsistency.ParsonsGuardRewrite
import DiophantineConsistency.ParsonsSpecialize

/-! An arbitrary finite universal prefix over a Σ₁ body is a Guard. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardPrefix ParsonsSpecialize

private theorem hierarchy_cast {n m : ℕ} (e : n = m) (A : ArithmeticSemiformula ℕ n)
    (h : Hierarchy 𝚺 1 A) : Hierarchy 𝚺 1 (cast (congrArg (ArithmeticSemiformula ℕ) e) A) := by
  cases e
  exact h

theorem closure {n : ℕ} (A : ArithmeticSemiformula ℕ n)
    (hA : Hierarchy 𝚺 1 A) : Guard (∀⁰* A) := by
  induction n with
  | zero => exact .sigma hA
  | succ n ih =>
      let e : n+1 = 1+n := Nat.add_comm n 1
      let A' : ArithmeticSemiformula ℕ (1+n) := cast (congrArg (ArithmeticSemiformula ℕ) e) A
      have hA' : Hierarchy 𝚺 1 A' := hierarchy_cast e A hA
      have hp : Hierarchy 𝚷 2 (∀⁰ (∀⁰^[n] A')) := by
        rw [Hierarchy.all_iff, Hierarchy.allItr_iff]
        exact hA'.strict_mono 𝚷 (s' := 2) (by decide)
      have hb : Guard ((∀⁰^[n] A').free) := by
        let K : ArithmeticSemiformula ℕ n := by
          simpa only [Nat.zero_add] using ((Rew.free).qpow n ▹ A')
        have hK : Hierarchy 𝚺 1 K := by
          simpa [K] using Hierarchy.rew ((Rew.free).qpow n) hA'
        have hi := ih K hK
        simpa [K, Rewriting.free, all_itr_closure] using hi
      have hresult : Guard (∀⁰* A') := by
        rw [all_closure_outer A']
        exact .all (∀⁰^[n] A') hp hb
      have hEq : (∀⁰* A') = ∀⁰* A := closure_cast e A
      rw [hEq] at hresult
      exact hresult
end DiophantineConsistency.ParsonsGuardClosure
