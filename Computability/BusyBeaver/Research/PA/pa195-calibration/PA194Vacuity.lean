import PA194BindTranslation

/-! Capture-avoiding vacuity at the Lean formula level. This is not a
primitive-recursive proof-template compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194Vacuity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindTranslation

/-- A fresh source label may be universally closed without changing truth. -/
theorem closeEvalGeneral {V : Type*} [Structure ℒₒᵣ V]
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
    · subst z; simp
    · simp [hz]
  rw [hb,hf]

theorem modelVacuity {V : Type*} [Structure ℒₒᵣ V] [Nonempty V]
    (a : Nat) (φ : ArithmeticFormula Nat) (h : ¬ φ.FVar? a) (e : Nat → V) :
    φ.Eval Fin.elim0 e ↔ (∀⁰ closeLabel a φ).Eval Fin.elim0 e := by
  rw [closeEvalGeneral]
  constructor
  · intro hp v
    have he : Function.funEqOn φ.FVar? e (Function.update e a v) := by
      intro x hx
      have hxa : x ≠ a := by intro heq; subst x; exact h hx
      simp [hxa]
    exact (Semiformula.eval_iff_of_funEqOn φ he).mp hp
  · intro hp
    letI : Inhabited V := Classical.inhabited_of_nonempty inferInstance
    have hv := hp (e a)
    simpa using hv

/-- Foundation PA proves each closed vacuity instance for any actual formula
with the selected label absent. This does not provide a PR proof code. -/
theorem PA_proves_vacuity (a : Nat) (φ : ArithmeticFormula Nat) (h : ¬ φ.FVar? a) :
    (𝗣𝗔 : ArithmeticTheory) ⊢ (φ 🡒 ∀⁰ closeLabel a φ).univCl := by
  letI : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔 : ArithmeticTheory) :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (inferInstance : 𝗜𝚺₀ ⪯ 𝗣𝗔)
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  have hv := modelVacuity a φ h e
  have he : (![ ] : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  simpa [Semiformula.Evalf, he] using hv.mp

#print axioms modelVacuity
#print axioms PA_proves_vacuity
end PA194Vacuity
