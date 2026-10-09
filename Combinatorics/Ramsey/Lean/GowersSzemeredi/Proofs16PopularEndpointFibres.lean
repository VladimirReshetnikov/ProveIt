import GowersSzemeredi.Proofs16ColumnTripleRepresentations

/-! Dense finite families with bounded fibres have many popular endpoints. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def popularEndpointFibres {X Y : Type*} [Fintype Y] [DecidableEq Y] (S : Finset X) (f : X → Y)
    (t : Real) : Finset Y := Finset.univ.filter (fun y => t ≤ ((S.filter (fun x => f x = y)).card : Real))

theorem popular_endpoint_fibres_dense {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset X) (f : X → Y) {K mu : Real} (hK : 0 < K) (hmu : 0 ≤ mu)
    (hcap : ∀ y, ((S.filter (fun x => f x = y)).card : Real) ≤ K)
    (hmass : mu*Fintype.card Y*K ≤ (S.card : Real)) :
    mu*Fintype.card Y/2 ≤ ((popularEndpointFibres S f (mu*K/2)).card : Real) := by
  let P := popularEndpointFibres S f (mu*K/2)
  let d (y : Y) : Real := (S.filter (fun x => f x = y)).card
  have hsum : (∑ y : Y, d y) = S.card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
      (f := f) (fun _ _ => Finset.mem_univ _)
    dsimp only [d]
    exact_mod_cast h.symm
  have hbound : ∀ y, d y ≤ (if y ∈ P then K else 0) + mu*K/2 := by
    intro y
    by_cases hy : y ∈ P
    · rw [if_pos hy]
      have h : 0 ≤ mu*K/2 := by positivity
      exact (hcap y).trans (by linarith)
    · rw [if_neg hy, zero_add]
      have hn : ¬mu*K/2 ≤ d y := by
        intro h
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      exact (lt_of_not_ge hn).le
  have htotal : (S.card : Real) ≤ P.card*K + Fintype.card Y*(mu*K/2) := by
    rw [← hsum]
    calc _ ≤ ∑ y : Y, ((if y ∈ P then K else 0) + mu*K/2) := Finset.sum_le_sum fun y _ => hbound y
      _ = _ := by simp [Finset.sum_add_distrib]
  change mu*Fintype.card Y/2 ≤ (P.card : Real)
  apply (mul_le_mul_iff_right₀ hK).mp
  nlinarith [htotal]

/-- Positive popular fibres occur in the image of the family. -/
theorem popular_endpoint_mem_image {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset X) (f : X → Y) {t : Real} (ht : 0 < t) {y : Y}
    (hy : y ∈ popularEndpointFibres S f t) : y ∈ S.image f := by
  have h := (Finset.mem_filter.mp hy).2
  have hp : (0 : Real) < (S.filter (fun x => f x = y)).card := ht.trans_le h
  have hp' : 0 < (S.filter (fun x => f x = y)).card := by exact_mod_cast hp
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hp'
  exact Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩

end LeanProofs.GowersSzemeredi
