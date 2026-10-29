import DiophantineConsistency.ParsonsCollectionRule
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCollectionSemantic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsCollectionRule

theorem semantic_step (D : ArithmeticSemiformula ℕ 2) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (f : ℕ → M)
    (h : (total D).Evalf f) : (step (collector D)).Evalf f := by
  simp [total, step, collector, Semiformula.eval_substs, Semiformula.eval_rew_q, Function.comp_def] at h ⊢
  intro k B hB
  simp [Matrix.fun_eq_vec_two] at h hB ⊢
  obtain ⟨y, hy⟩ := h k
  refine ⟨B + y + 1, ?_⟩
  intro i hi
  have hle : i ≤ k := Arithmetic.le_iff_lt_succ.mpr hi
  rcases lt_or_eq_of_le hle with hlt | rfl
  · obtain ⟨z, hz, hD⟩ := hB i hlt
    refine ⟨z, ?_, hD⟩
    exact lt_of_lt_of_le hz (by simp)
  · refine ⟨y, ?_, hy⟩
    apply Arithmetic.le_iff_lt_succ.mp
    simp

/-- PA-minus proves the universal closure of the finite-extension step. -/
theorem step_closed (D : ArithmeticSemiformula ℕ 2) :
    𝗣𝗔⁻ ⊢ (total D 🡒 step (collector D)).univCl := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  classical
  by_cases ht : (total D).Evalf f
  · simp [Semiformula.imp_eq, ht, semantic_step D M f ht]
  · simp [Semiformula.imp_eq, ht]

/-- When the finite-extension statement is closed, completeness provides an
actual proof in the rule calculus without any open-variable specialization. -/
noncomputable def step_proof_closed (D : ArithmeticSemiformula ℕ 2)
    (hClosed : (total D 🡒 step (collector D)).freeVariables = ∅) :
    ParsonsRule.Proof 𝗣𝗔⁻ (total D 🡒 step (collector D)) := by
  have h := ParsonsRuleEmbedding.embedTheory (step_closed D).some
  simpa [Semiformula.univCl'_eq_self_of _ hClosed] using h

/-- A complete collection-rule proof transformer for parameter-free instances.
No finite-extension premise is assumed. -/
noncomputable def collect_closed (D : ArithmeticSemiformula ℕ 2)
    (hD : Hierarchy 𝚺 1 D)
    (hClosed : (total D 🡒 step (collector D)).freeVariables = ∅)
    (hTotal : ParsonsRule.Proof 𝗣𝗔⁻ (total D)) :
    ParsonsRule.Proof 𝗣𝗔⁻ (∀⁰ collector D) :=
  collect_if_step D hD hTotal (step_proof_closed D hClosed)

end DiophantineConsistency.ParsonsCollectionSemantic
