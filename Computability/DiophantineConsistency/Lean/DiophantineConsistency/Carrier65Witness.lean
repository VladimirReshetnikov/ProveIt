import DiophantineConsistency.Carrier65
import DiophantineConsistency.CarrierRankBounds
import DiophantineConsistency.FirstPellCarrier

/-!
# Recovering the omitted witness from the actual Carrier65 polynomial

Every hypothesis concerns the four fixed scalar ports, positivity of the
fourteen independent coordinates, or a zero of the literal polynomial.
The rank window, first-root sign and positive omitted quotient are all
derived. Binding the native coefficient recipe and refutation predicate
remains a further obligation.
-/

namespace DiophantineConsistency.Carrier65Witness

open Carrier65

/-- The fixed-port box used by the uniform ordinary Carrier65 theorem. -/
structure PortBounds (p : Fin 4 → ℤ) : Prop where
  beta_min : 31 ≤ p 0
  K_pos : 0 < p 1
  MC_pos : 0 < p 2
  MC_lt : p 2 < p 0
  MF_gt : p 0 < p 3
  MF_lt : p 3 < 2 * p 0

theorem positive_zero_rank_window (p : Fin 4 → ℤ) (hp : PortBounds p)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    0 < (core p v).C ∧ 1 < (core p v).rank ∧
      (core p v).rank + 2 < (core p v).E := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  have hq : 3 ≤ (core p v).q := by
    have hJ : 1 ≤ v 0 := hv 0
    have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt hb)
    change 3 ≤ p 0 * v 0 + 1
    have := hp.beta_min
    nlinarith only [hmul, this]
  have hW := ((value_zero_iff_norms p v hb hv).mp hz).2.2.2.2
  rw [transport_shape] at hW
  have hC := CarrierRankBounds.carrier_pos_of_transport (by omega : 1 < (core p v).q)
    hp.K_pos (hv 8) (hv 1) (hv 3) hW
  have hMF : 0 < p 3 := lt_trans hb hp.MF_gt
  have hr := CarrierRankBounds.rank_window hq (hv 0) (q_sub_one p v).symm
    hp.MC_pos hp.MC_lt hMF hp.MF_lt (hv 1) (hv 2) hC (hv 8) (hv 7)
  unfold CarrierRankBounds.rank at hr
  rw [← rank_shape p v, ← scale_shape p v] at hr
  exact ⟨hC, hr⟩

/-- All positive zeros of the actual fourteen-coordinate equation restore
one and only one positive omitted index quotient. -/
theorem positive_zero_restores_index (p : Fin 4 → ℤ) (hp : PortBounds p)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    0 < (core p v).tau ∧
      ∃! h : ℤ, 0 < h ∧ (core p v).k - h * (core p v).E - (core p v).rank = 1 := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  obtain ⟨_, hR, hcap⟩ := positive_zero_rank_window p hp v hv hz
  have hscales := scales_pos p v hb hv
  have hE : 0 < (core p v).E := hscales.2.2.1
  have hY : 0 < (core p v).Y := hscales.2.1
  have hk : 0 < (core p v).k := add_pos (hv 10) (hv 11)
  have hnorm := ((value_zero_iff_norms p v hb hv).mp hz).1
  rw [first_shape] at hnorm
  obtain ⟨ht, h, hh, heq⟩ := FirstPellCarrier.restore_quotient hE hY hk (hv 9)
    hR hcap (carrier_shape p v) hnorm
  refine ⟨ht, h, ⟨hh, heq⟩, ?_⟩
  intro other hother
  exact FirstPellCarrier.quotient_unique (ne_of_gt hE) hother.2 heq

/-- The same recovery applies directly to the actual multivariate
polynomial, with no supplied rank bound or first-root sign premise. -/
theorem polynomial_zero_restores_index (p : Fin 4 → ℤ) (hp : PortBounds p)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (polynomial p) = 0) :
    0 < (core p v).tau ∧
      ∃! h : ℤ, 0 < h ∧ (core p v).k - h * (core p v).E - (core p v).rank = 1 := by
  rw [eval_polynomial] at hz
  exact positive_zero_restores_index p hp v hv hz

end DiophantineConsistency.Carrier65Witness
