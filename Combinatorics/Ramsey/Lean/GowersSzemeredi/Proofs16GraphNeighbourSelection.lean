import GowersSzemeredi.Proofs16GraphCodegrees

/-! Choose a large neighbourhood containing few deficient pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- A dense graph has a neighbourhood of size at least `delta*n/2`
with at most one sixteenth of its ordered pairs below codegree
`delta^2*n/64`. -/
theorem exists_large_neighbourhood_few_bad_pairs {V : Type*} [Fintype V] [Nonempty V]
    (G : V → V → Prop) (hG : ∀ a b, G a b → G b a) {delta : Real} (hd : 0 < delta)
    (hedges : delta * (Fintype.card V : Real)^2 ≤ ∑ x : V, ((graphNeighbours G x).card : Real)) :
    ∃ x : V,
      delta * Fintype.card V / 2 ≤ ((graphNeighbours G x).card : Real) ∧
      ((graphBadPairs G (delta^2 * Fintype.card V / 64) x).card : Real) ≤
        ((graphNeighbours G x).card : Real)^2 / 16 := by
  let n : Real := Fintype.card V
  let d (x : V) : Real := (graphNeighbours G x).card
  let b (x : V) : Real := (graphBadPairs G (delta^2*n/64) x).card
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hb : ∑ x : V, b x ≤ (delta^2*n/64)*n^2 := graph_bad_pairs_sum_le G hG (by positivity)
  have hsum : delta^2*n^3/2 ≤ ∑ x : V, (delta*n*d x-32*b x) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have he := mul_le_mul_of_nonneg_left hedges (show 0 ≤ delta*n by positivity)
    dsimp only [n, d] at *
    nlinarith
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ
    (fun x => delta*n*d x-32*b x) Finset.univ_nonempty
  have hmax : (∑ y : V, (delta*n*d y-32*b y)) ≤ n*(delta*n*d x-32*b x) := by
    calc _ ≤ ∑ _y : V, (delta*n*d x-32*b x) := Finset.sum_le_sum fun y _ => hx y (Finset.mem_univ _)
      _ = _ := by simp [n]; ring
  have hscore : delta^2*n^2/2 ≤ delta*n*d x-32*b x := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith [hsum.trans hmax]
  have hbx : 0 ≤ b x := Nat.cast_nonneg _
  have hdx : 0 ≤ d x := Nat.cast_nonneg _
  have hsize : delta*n/2 ≤ d x := by
    apply (mul_le_mul_iff_left₀ (show 0 < delta*n by positivity)).mp
    nlinarith
  refine ⟨x, hsize, ?_⟩
  have hprod := mul_le_mul_of_nonneg_right hsize hdx
  nlinarith [sq_nonneg (delta*n)]

end LeanProofs.GowersSzemeredi
