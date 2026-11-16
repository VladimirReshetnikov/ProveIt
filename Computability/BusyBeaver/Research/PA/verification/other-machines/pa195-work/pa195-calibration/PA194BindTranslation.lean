import DiophantineConsistency.PRAHistoryInsertCode

/-! Capture-avoiding closure of a source variable label. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace PA194BindTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Close a named source label by mapping it to the fresh de Bruijn binder.
Existing bound indices are shifted automatically under nested quantifiers. -/
def closeLabel (a : Nat) (φ : ArithmeticFormula Nat) : ArithmeticSemiformula Nat 1 :=
  (Rew.bind Fin.elim0 (fun z => if z = a then #0 else &z) : Rew ℒₒᵣ Nat 0 Nat 1) ▹ φ

theorem closeLabel_free (a x : Nat) (φ : ArithmeticFormula Nat)
    (h : (closeLabel a φ).FVar? x) : x ≠ a ∧ φ.FVar? x := by
  unfold closeLabel at h
  rcases Semiformula.fvar?_rew (φ := φ)
    (ω := (Rew.bind Fin.elim0 (fun z => if z = a then #0 else &z) : Rew ℒₒᵣ Nat 0 Nat 1)) h with
    (⟨i,_⟩ | ⟨z,hz,hx⟩)
  · exact Fin.elim0 i
  · by_cases hza : z = a
    · simp [hza] at hx
    · simp [hza] at hx
      subst z
      exact ⟨hza,hz⟩
/-- Closing and quantifying a label has exactly the expected valuation
semantics, including when the formula has nested quantifiers. -/
theorem closeLabel_eval {V : Type*} [ORingStructure V]
    (a : Nat) (φ : ArithmeticFormula Nat) (e : Nat → V) :
    (∀⁰ closeLabel a φ).Eval Fin.elim0 e ↔
      ∀ v : V, φ.Eval Fin.elim0 (Function.update e a v) := by
  simp only [Semiformula.eval_all]
  apply forall_congr'
  intro v
  unfold closeLabel
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := ℒₒᵣ) (v :> Fin.elim0) e ∘
      (Rew.bind Fin.elim0 (fun z => if z = a then #0 else &z) : Rew ℒₒᵣ Nat 0 Nat 1) ∘ Semiterm.bvar) =
      (Fin.elim0 : Fin 0 → V) := Subsingleton.elim _ _
  have hf : (Semiterm.val (L := ℒₒᵣ) (v :> Fin.elim0) e ∘
      (Rew.bind Fin.elim0 (fun z => if z = a then #0 else &z) : Rew ℒₒᵣ Nat 0 Nat 1) ∘ Semiterm.fvar) =
      Function.update e a v := by
    funext z
    by_cases hz : z = a
    · subst z
      simp
    · simp [hz]
  rw [hb,hf]

#print axioms closeLabel_free
#print axioms closeLabel_eval
end PA194BindTranslation
