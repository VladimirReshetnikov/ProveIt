import GowersSzemeredi.Proofs16TripleEndpointFibres

/-! Count choices from two prescribed fibres over a connecting relation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def fibreGluings {Q X Y U V : Type*} [DecidableEq U] [DecidableEq V] (C : Finset Q) (S : Finset X) (R : Finset Y)
    (f : X → U) (g : Y → V) (u : Q → U) (v : Q → V) : Finset (Q × X × Y) :=
  (C ×ˢ (S ×ˢ R)).filter (fun t => f t.2.1 = u t.1 ∧ g t.2.2 = v t.1)

theorem fibreGluings_card {Q X Y U V : Type*} [DecidableEq U] [DecidableEq V] (C : Finset Q) (S : Finset X) (R : Finset Y)
    (f : X → U) (g : Y → V) (u : Q → U) (v : Q → V) :
    (fibreGluings C S R f g u v).card =
      ∑ q ∈ C, (S.filter (fun x => f x = u q)).card * (R.filter (fun y => g y = v q)).card := by
  simp only [fibreGluings, Finset.card_filter, Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = u q <;> by_cases hy : g y = v q <;> simp [hx,hy]

/-- Each connecting quadruple contributes the product of its two
available representation counts. -/
theorem fibreGluings_card_lower {Q X Y U V : Type*} [DecidableEq U] [DecidableEq V] (C : Finset Q) (S : Finset X) (R : Finset Y)
    (f : X → U) (g : Y → V) (u : Q → U) (v : Q → V) {k l : Real}
    (hl : 0 ≤ l)
    (hS : ∀ q ∈ C, k ≤ ((S.filter (fun x => f x = u q)).card : Real))
    (hR : ∀ q ∈ C, l ≤ ((R.filter (fun y => g y = v q)).card : Real)) :
    (C.card : Real)*k*l ≤ (fibreGluings C S R f g u v).card := by
  have heq : ((fibreGluings C S R f g u v).card : Real) =
      ∑ q ∈ C, ((S.filter (fun x => f x = u q)).card : Real) * (R.filter (fun y => g y = v q)).card := by
    exact_mod_cast fibreGluings_card C S R f g u v
  rw [heq]
  calc _ = ∑ _q ∈ C, k*l := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun q hq => mul_le_mul (hS q hq) (hR q hq) hl (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
