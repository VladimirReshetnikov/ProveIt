import GowersSzemeredi.Proofs16PopularEndpointFibres

/-! Popular fibres retain mass, and every subset of popular endpoints
retains a controlled number of original configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem fibre_filter_mass_lower {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (f : X → Y) (P : Finset Y) {tau : Real}
    (hP : ∀ y ∈ P, tau ≤ ((S.filter fun x => f x = y).card : Real)) :
    tau*P.card ≤ ((S.filter fun x => f x ∈ P).card : Real) := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter S P f
  have hcR : (∑ y ∈ P, ((S.filter fun x => f x = y).card : Real)) =
      (S.filter fun x => f x ∈ P).card := by exact_mod_cast hc
  rw [← hcR]
  calc tau*P.card = ∑ _y ∈ P, tau := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum hP

/-- Discarding endpoints below threshold loses at most the threshold
times the size of the endpoint space, with no fibre upper-bound assumption. -/
theorem popular_fibre_retained_mass {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset X) (f : X → Y) {tau : Real} (htau : 0 ≤ tau) :
    (S.card : Real)-Fintype.card Y*tau ≤
      ((S.filter fun x => f x ∈ popularEndpointFibres S f tau).card : Real) := by
  let P := popularEndpointFibres S f tau
  have hbad : ∀ y ∈ Pᶜ, ((S.filter fun x => f x = y).card : Real) ≤ tau := by
    intro y hy
    have hn := Finset.mem_compl.mp hy
    exact (lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))).le
  have hc := Finset.sum_card_fiberwise_eq_card_filter S Pᶜ f
  have hcR : (∑ y ∈ Pᶜ, ((S.filter fun x => f x = y).card : Real)) =
      ((S.filter fun x => f x ∉ P).card : Real) := by
    exact_mod_cast (by simpa only [Finset.mem_compl] using hc)
  have hb : ((S.filter fun x => f x ∉ P).card : Real) ≤ Fintype.card Y*tau := by
    rw [← hcR]
    calc _ ≤ ∑ _y ∈ Pᶜ, tau := Finset.sum_le_sum hbad
      _ = (Pᶜ.card : Real)*tau := by simp
      _ ≤ Fintype.card Y*tau := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ Pᶜ) htau
  have hsplit : ((S.filter fun x => f x ∈ P).card : Real)+
      (S.filter fun x => f x ∉ P).card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S) (fun x => f x ∈ P)
  change (S.card : Real)-Fintype.card Y*tau ≤ ((S.filter fun x => f x ∈ P).card : Real)
  linarith

end LeanProofs.GowersSzemeredi
