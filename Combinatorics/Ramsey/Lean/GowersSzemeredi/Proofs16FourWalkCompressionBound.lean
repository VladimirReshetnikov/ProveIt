import GowersSzemeredi.Proofs16GraphFourWalks

/-! Four-walk compression with an explicit exceptional-path bound.
Only two successive common-neighborhood implications are needed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

theorem graph_four_walks_le_of_small_common {V : Type*} [Fintype V]
    (G H : V → V → Prop) (hG : ∀ x y, G x y → G y x)
    {t : Real} (ht : 0 ≤ t)
    (hcomp : ∀ x y, t ≤ ((graphCommonNeighbours G x y).card : Real) → H x y)
    (u v : V) (hsmall : ((graphCommonNeighbours H u v).card : Real) ≤ t) :
    ((graphFourWalks G u v).card : Real) ≤ 2*t*(Fintype.card V : Real)^2 := by
  let n : Real := Fintype.card V
  let M := graphCommonNeighbours H u v
  let a := fun z => ((graphCommonNeighbours G u z).card : Real)
  let b := fun z => ((graphCommonNeighbours G v z).card : Real)
  have ha (z : V) : 0 ≤ a z ∧ a z ≤ n :=
    ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (Finset.card_le_univ _)⟩
  have hb (z : V) : 0 ≤ b z ∧ b z ≤ n :=
    ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (Finset.card_le_univ _)⟩
  have hpoint (z : V) : a z*b z ≤ t*n + if z ∈ M then n^2 else 0 := by
    by_cases hz : z ∈ M
    · rw [if_pos hz]
      have h := mul_le_mul (ha z).2 (hb z).2 (hb z).1 (by dsimp [n]; positivity)
      nlinarith [mul_nonneg ht (show 0 ≤ n by dsimp [n]; positivity)]
    · rw [if_neg hz,add_zero]
      have hnot : ¬ (t ≤ a z ∧ t ≤ b z) := by
        rintro ⟨h₁,h₂⟩
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcomp u z h₁,hcomp v z h₂⟩)
      by_cases h₁ : t ≤ a z
      · have h₂ : b z ≤ t := (lt_of_not_ge (fun h₂ => hnot ⟨h₁,h₂⟩)).le
        calc a z*b z ≤ n*t := mul_le_mul (ha z).2 h₂ (hb z).1 (by dsimp [n]; positivity)
          _ = t*n := mul_comm _ _
      · exact mul_le_mul (le_of_lt (lt_of_not_ge h₁)) (hb z).2 (hb z).1 ht
  have heq : ((graphFourWalks G u v).card : Real) = ∑ z, a z*b z := by
    dsimp only [a,b]
    exact_mod_cast graph_four_walks_card G hG u v
  rw [heq]
  calc _ ≤ ∑ z : V, (t*n + if z ∈ M then n^2 else 0) := Finset.sum_le_sum (fun z _ => hpoint z)
    _ = n*(t*n)+(M.card : Real)*n^2 := by simp [Finset.sum_add_distrib,n]
    _ ≤ n*(t*n)+t*n^2 := add_le_add_right (mul_le_mul_of_nonneg_right hsmall (sq_nonneg n)) _
    _ = _ := by dsimp [n]; ring

end LeanProofs.GowersSzemeredi
