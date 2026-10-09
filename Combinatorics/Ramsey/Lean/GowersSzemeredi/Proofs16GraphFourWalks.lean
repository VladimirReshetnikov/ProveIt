import GowersSzemeredi.Proofs16GraphCommonCodegrees

/-! A dense symmetric graph has a large vertex set joined by many
walks of length four. Repeated vertices are allowed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def graphFourWalks {V : Type*} [Fintype V] (G : V → V → Prop) (u v : V) : Finset (V × V × V) :=
  Finset.univ.filter (fun t => G u t.1 ∧ G t.1 t.2.1 ∧ G t.2.1 t.2.2 ∧ G t.2.2 v)

theorem graph_four_walks_card {V : Type*} [Fintype V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) (u v : V) :
    (graphFourWalks G u v).card =
      ∑ z : V, (graphCommonNeighbours G u z).card * (graphCommonNeighbours G v z).card := by
  simp only [graphFourWalks, Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [graphCommonNeighbours, Finset.card_filter, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hsym (x y : V) : G x y ↔ G y x := ⟨hG x y, hG y x⟩
  rw [hsym a z, hsym b v]
  by_cases h1 : G u a <;> by_cases h2 : G z a <;> by_cases h3 : G v b <;> by_cases h4 : G z b <;>
    simp [h1, h2, h3, h4]

/-- Ordered-edge density `delta` gives a set of at least `3*delta*n/8`
vertices and at least `delta^5*n^3/16384` four-walks between every two. -/
theorem exists_dense_four_walk_set {V : Type*} [Fintype V] [Nonempty V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) {delta : Real} (hd : 0 < delta)
    (hedges : delta * (Fintype.card V : Real)^2 ≤ ∑ x : V, ((graphNeighbours G x).card : Real)) :
    ∃ T : Finset V, 3*delta*Fintype.card V/8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T,
        delta^5*(Fintype.card V : Real)^3/16384 ≤ ((graphFourWalks G u v).card : Real) := by
  obtain ⟨T, hT, hcommon⟩ := exists_dense_common_codegree_set G hG hd hedges
  refine ⟨T, hT, ?_⟩
  intro u hu v hv
  let tau := delta^2*(Fintype.card V : Real)/64
  let M := Finset.univ.filter (fun z => tau ≤ ((graphCommonNeighbours G u z).card : Real) ∧
    tau ≤ ((graphCommonNeighbours G v z).card : Real))
  have hM : delta*Fintype.card V/4 ≤ (M.card : Real) := hcommon u hu v hv
  have heq : ((graphFourWalks G u v).card : Real) =
      ∑ z : V, ((graphCommonNeighbours G u z).card : Real) * (graphCommonNeighbours G v z).card := by
    exact_mod_cast graph_four_walks_card G hG u v
  have hlow : (M.card : Real)*tau^2 ≤ ((graphFourWalks G u v).card : Real) := by
    rw [heq]
    calc _ = ∑ _z ∈ M, tau^2 := by simp
      _ ≤ ∑ z ∈ M, ((graphCommonNeighbours G u z).card : Real) * (graphCommonNeighbours G v z).card := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨hz1, hz2⟩ := (Finset.mem_filter.mp hz).2
        simpa only [pow_two] using mul_le_mul hz1 hz2 (by dsimp [tau]; positivity) (Nat.cast_nonneg _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h := (mul_le_mul_of_nonneg_right hM (sq_nonneg tau)).trans hlow
  dsimp only [tau] at h
  calc delta^5*(Fintype.card V : Real)^3/16384 =
      (delta*Fintype.card V/4)*(delta^2*(Fintype.card V : Real)/64)^2 := by ring
    _ ≤ _ := h

end LeanProofs.GowersSzemeredi
