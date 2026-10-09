import GowersSzemeredi.Proofs16GraphFourWalks

/-! Apply four-walk extraction to a finite edge set with a prescribed
vertex carrier, as supplied by the coherent column graph. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

theorem graph_edge_degree_sum {V : Type*} [Fintype V] (E : Finset (V × V)) :
    (∑ x : V, (graphNeighbours (fun u v => (u,v) ∈ E) x).card) = E.card := by
  calc _ = (Finset.univ.filter (fun p : V × V => p ∈ E)).card := by
          simp only [graphNeighbours, Finset.card_filter, Fintype.sum_prod_type]
    _ = E.card := by simp

/-- The extracted vertex set stays in the original carrier. -/
theorem exists_dense_four_walk_set_on {V : Type*} [Fintype V] [Nonempty V]
    (X : Finset V) (E : Finset (V × V)) (hEX : E ⊆ X ×ˢ X)
    (hsym : ∀ p ∈ E, p.swap ∈ E) {delta : Real} (hd : 0 < delta)
    (hE : delta*(Fintype.card V : Real)^2 ≤ E.card) :
    ∃ T ⊆ X, 3*delta*Fintype.card V/8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T,
        delta^5*(Fintype.card V : Real)^3/16384 ≤
          ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real) := by
  let G (a b : V) := (a,b) ∈ E
  have hG : ∀ a b, G a b → G b a := fun a b h => hsym (a,b) h
  have hdegrees : delta*(Fintype.card V : Real)^2 ≤ ∑ x : V, ((graphNeighbours G x).card : Real) := by
    have heq : (∑ x : V, ((graphNeighbours G x).card : Real)) = E.card := by
      exact_mod_cast graph_edge_degree_sum E
    exact heq.symm ▸ hE
  obtain ⟨T, hT, hwalk⟩ := exists_dense_four_walk_set G hG hd hdegrees
  refine ⟨T, ?_, hT, hwalk⟩
  intro u hu
  have h := hwalk u hu u hu
  have hn : (0 : Real) < Fintype.card V := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hpos : (0 : Real) < (graphFourWalks G u u).card := lt_of_lt_of_le (by positivity) h
  have hc : 0 < (graphFourWalks G u u).card := by exact_mod_cast hpos
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hc
  have ht' : G u t.1 ∧ G t.1 t.2.1 ∧ G t.2.1 t.2.2 ∧ G t.2.2 u := by
    simpa only [graphFourWalks, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  have he : (u,t.1) ∈ E := ht'.1
  exact (Finset.mem_product.mp (hEX he)).1

end LeanProofs.GowersSzemeredi
