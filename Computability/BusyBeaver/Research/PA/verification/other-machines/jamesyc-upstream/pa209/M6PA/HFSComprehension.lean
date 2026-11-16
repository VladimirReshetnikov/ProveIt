module
public import M6PA.Theory
public import Foundation.FirstOrder.Arithmetic.HFS.Basic
@[expose] public section

/-! Full formula separation in every PA model, not only in standard finite HFS.
This is the discriminating arithmetic ingredient for the native pointed bundle;
connecting that bundle's exact named decoder remains a separate proof. -/
namespace M6.PA.HFSComprehension
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Every finite arithmetic formula belongs to some positive finite level. -/
theorem formula_rank {ξ : Type*} {n : Nat} (φ : ArithmeticSemiformula ξ n) :
    ∃ k : Nat, ∀ Γ, ℬ[<,ℒₒᵣ].Hierarchy Γ (k+1) φ := by
  induction φ with
  | verum => exact ⟨0,fun Γ => .verum Γ 1 _⟩
  | falsum => exact ⟨0,fun Γ => .falsum Γ 1 _⟩
  | rel r v => exact ⟨0,fun Γ => .rel Γ 1 r v⟩
  | nrel r v => exact ⟨0,fun Γ => .nrel Γ 1 r v⟩
  | and p q ihp ihq =>
    rcases ihp with ⟨k,hk⟩
    rcases ihq with ⟨j,hj⟩
    exact ⟨max k j,fun Γ => .and ((hk Γ).mono (by omega)) ((hj Γ).mono (by omega))⟩
  | or p q ihp ihq =>
    rcases ihp with ⟨k,hk⟩
    rcases ihq with ⟨j,hj⟩
    exact ⟨max k j,fun Γ => .or ((hk Γ).mono (by omega)) ((hj Γ).mono (by omega))⟩
  | all p ih =>
    rcases ih with ⟨k,hk⟩
    refine ⟨k+1,?_⟩
    intro Γ
    cases Γ
    · exact (hk 𝚷).dummy_sigma
    · exact ((hk 𝚷).all).accum 𝚷
  | exs p ih =>
    rcases ih with ⟨k,hk⟩
    refine ⟨k+1,?_⟩
    intro Γ
    cases Γ
    · exact ((hk 𝚺).exs).accum 𝚺
    · exact (hk 𝚺).dummy_pi

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Separation for any arithmetic formula with arbitrary model parameters. -/
theorem bounded_separation (φ : ArithmeticSemiformula Nat 1) (env : Nat → V) (m : V) :
    ∃ s : V, ∀ x, x ∈ s ↔ x < m ∧ φ.Eval ![x] env := by
  rcases formula_rank φ with ⟨k,hk⟩
  let : Fact (1 ≤ k+1) := ⟨by omega⟩
  have hp : 𝚺ᴬ_[k+1]-Predicate (fun x : V => φ.Eval ![x] env) :=
    Bounding.definablePred_of_hierarchy (hk 𝚺) env
  obtain ⟨s,hs,hsep⟩ := finset_comprehension hp m
  refine ⟨s,fun x => ⟨?_,?_⟩⟩
  · intro hx
    have hm : x < m := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hx) hs)
    exact ⟨hm,(hsep x hm).mp hx⟩
  · rintro ⟨hm,hx⟩
    exact (hsep x hm).mpr hx

/-- The complete pointed-separation clause needed by the unchanged bundle:
all selected members of a are retained, every member satisfies the property,
and the distinguished point b is included whenever it satisfies the property. -/
theorem pointed_separation (φ : ArithmeticSemiformula Nat 1) (env : Nat → V) (a b : V) :
    ∃ s : V, (∀ x, (x ∈ a → φ.Eval ![x] env → x ∈ s) ∧
      (x ∈ s → φ.Eval ![x] env)) ∧ (φ.Eval ![b] env → b ∈ s) := by
  obtain ⟨s,hs⟩ := bounded_separation φ env (a+b+1)
  refine ⟨s,?_,?_⟩
  · intro x
    constructor
    · intro hxa hp
      apply (hs x).mpr
      refine ⟨?_,hp⟩
      have hxa' : x < a := lt_of_mem hxa
      have hab : a ≤ a+b := by simp
      exact lt_trans (lt_of_lt_of_le hxa' hab) (by simp)
    · intro hxs
      exact ((hs x).mp hxs).2
  · intro hp
    apply (hs b).mpr
    refine ⟨?_,hp⟩
    have hab : b ≤ a+b := by simp
    exact lt_of_le_of_lt hab (by simp)

/-- Object-language version, universally closed over all finite parameters. -/
def pointedSchema (φ : ArithmeticSemiformula Nat 1) : ArithmeticProposition :=
  “∀ a b, ∃ s,
    (∀ x, (x ∈ a → !φ x → x ∈ s) ∧ (x ∈ s → !φ x)) ∧
    (!φ b → b ∈ s)”

theorem pa_proves_pointedSchema (φ : ArithmeticSemiformula Nat 1) :
    theory ⊢ (pointedSchema φ).univCl := by
  apply Arithmetic.complete.{0} theory _
  intro W _ _
  simp only [models_iff,Semiformula.eval_univCl]
  intro env
  simpa [pointedSchema] using pointed_separation (V := W) φ env

#print axioms pa_proves_pointedSchema
#print axioms formula_rank
#print axioms bounded_separation
#print axioms pointed_separation
end M6.PA.HFSComprehension

