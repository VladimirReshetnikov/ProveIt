import GowersSzemeredi.Proofs16CoordinateRestrictionCount

/-! Double counting selects one global assignment that realizes at least
its average number of configurations. Balance is expressed without division. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_balanced_incidence_fiber {X P : Type*} [Fintype X] [Nonempty X]
    (H : Finset P) (R : X → P → Prop) (K : Nat)
    (hbalance : ∀ p ∈ H, ((Finset.univ.filter fun x : X => R x p).card)*K = Fintype.card X) :
    ∃ x : X, H.card ≤ K*(H.filter (R x)).card := by
  have hswap : (∑ x : X, (H.filter (R x)).card) =
      ∑ p ∈ H, (Finset.univ.filter fun x : X => R x p).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hsum : (∑ x : X, K*(H.filter (R x)).card) = H.card*Fintype.card X := by
    rw [← Finset.mul_sum,hswap,Finset.mul_sum]
    calc _ = ∑ _p ∈ H, Fintype.card X := by
           apply Finset.sum_congr rfl
           intro p hp
           simpa only [Nat.mul_comm] using hbalance p hp
      _ = _ := by simp
  have hle : (∑ _x : X, H.card) ≤ ∑ x : X, K*(H.filter (R x)).card := by
    rw [hsum]
    simp [Nat.mul_comm]
  obtain ⟨x,_,hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact ⟨x,hx⟩

end LeanProofs.GowersSzemeredi
