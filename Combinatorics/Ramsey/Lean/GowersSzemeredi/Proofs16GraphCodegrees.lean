import GowersSzemeredi.Proofs16ColumnGraph

/-! Double counting deficient pairs inside graph neighbourhoods. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def graphNeighbours {V : Type*} [Fintype V] (G : V → V → Prop) (x : V) : Finset V :=
  Finset.univ.filter (G x)

def graphCommonNeighbours {V : Type*} [Fintype V] (G : V → V → Prop) (u v : V) : Finset V :=
  Finset.univ.filter (fun x => G u x ∧ G v x)

def graphBadPairs {V : Type*} [Fintype V] (G : V → V → Prop) (tau : Real) (x : V) : Finset (V × V) :=
  Finset.univ.filter (fun p => G x p.1 ∧ G x p.2 ∧ (graphCommonNeighbours G p.1 p.2).card < tau)

/-- Count a marked pair once for every common neighbour. -/
theorem graph_neighbour_pair_double_count {V : Type*} [Fintype V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) (B : V → V → Prop) :
    (∑ x : V, (Finset.univ.filter (fun p : V × V => G x p.1 ∧ G x p.2 ∧ B p.1 p.2)).card) =
      ∑ u : V, ∑ v : V, if B u v then (graphCommonNeighbours G u v).card else 0 := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  have hsym (a b : V) : G a b ↔ G b a := ⟨hG a b, hG b a⟩
  by_cases hB : B u v
  · simp only [hB, and_true, ite_true, graphCommonNeighbours, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    rw [hsym x u, hsym x v]
  · simp only [hB, and_false, ite_false, Finset.sum_const_zero]

/-- Low-codegree pairs make a small total contribution over all
neighbourhoods. -/
theorem graph_bad_pairs_sum_le {V : Type*} [Fintype V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) {tau : Real} (htau : 0 ≤ tau) :
    (∑ x : V, ((graphBadPairs G tau x).card : Real)) ≤ tau * (Fintype.card V : Real)^2 := by
  have heq := graph_neighbour_pair_double_count G hG
    (fun u v => (graphCommonNeighbours G u v).card < tau)
  have heqR : (∑ x : V, ((graphBadPairs G tau x).card : Real)) =
      ∑ u : V, ∑ v : V,
        if (graphCommonNeighbours G u v).card < tau then ((graphCommonNeighbours G u v).card : Real) else 0 := by
    exact_mod_cast heq
  rw [heqR]
  calc _ ≤ ∑ _u : V, ∑ _v : V, tau := by
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro v _
          split_ifs with h
          · exact h.le
          · exact htau
    _ = tau * (Fintype.card V : Real)^2 := by simp; ring

end LeanProofs.GowersSzemeredi
