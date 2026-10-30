import DiophantineConsistency.ParsonsGuardTree
import DiophantineConsistency.ParsonsGuardClosure
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStrictPrefixTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardTree ParsonsRule ParsonsBlock

theorem of_guard {P : Proposition ℒₒᵣ} (h : ParsonsGuardPrefix.Guard P) : Tree P := by
  induction h with
  | sigma h => exact .sigma h
  | all A h _ ih => exact .all A h ih

theorem negative_closure {n : ℕ} (D : ArithmeticSemiformula ℕ n) (hD : Hierarchy 𝚺 0 D) :
    Tree (∼(∃⁰* D)) := by
  have hneg : Hierarchy 𝚺 1 (∼D) := (Hierarchy.neg hD).accum 𝚺
  have h := of_guard (ParsonsGuardClosure.closure (∼D) hneg)
  simpa using h

theorem negative_free {n : ℕ} (D : ArithmeticSemiformula ℕ (1+n)) (hD : Hierarchy 𝚺 0 D) :
    Tree (∼((∃⁰^[n] D).free)) := by
  let D' : ArithmeticSemiformula ℕ (0+n) := (Rew.free).qpow n ▹ D
  have hD' : Hierarchy 𝚺 0 D' := Hierarchy.rew _ hD
  have hh := negative_closure D' hD'
  simpa [D', Rewriting.free, ParsonsBlock.itr_closure] using hh

theorem strict_step {n : ℕ} (D : ArithmeticSemiformula ℕ (1+n)) (hD : Hierarchy 𝚺 0 D) :
    Tree (step (∃⁰^[n] D)) := by
  let φ : ArithmeticSemiformula ℕ 1 := ∃⁰^[n] D
  have hφ : Hierarchy 𝚺 1 φ := Hierarchy.exsItr_iff.mpr (hD.mono (by decide))
  have hp : Hierarchy 𝚷 2 (step φ) := ParsonsSide.step_pi_two φ hφ
  have hn : Tree (∼φ.free) := negative_free D hD
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

theorem strict_negative {n : ℕ} (D : ArithmeticSemiformula ℕ (1+n)) (hD : Hierarchy 𝚺 0 D)
    (t : SyntacticTerm ℒₒᵣ) : Tree (∼((∃⁰^[n] D)/[t])) := by
  have hD' : Hierarchy 𝚺 0 (advance D t) := Hierarchy.rew _ hD
  have hh := negative_closure (advance D t) hD'
  rw [ParsonsBlock.opening]
  exact hh
end DiophantineConsistency.ParsonsStrictPrefixTree
