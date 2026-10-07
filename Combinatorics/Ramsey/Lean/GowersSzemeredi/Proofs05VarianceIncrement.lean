import GowersSzemeredi.Proofs05ProgressionVariance
import GowersSzemeredi.Proofs05ProperDirections

/-! A density increment on a proper progression from the second moment.
For every cyclic modulus, `N ≥ L³` suffices for a gain `(1-δ)/(2L)`.
This proves the low-correlation branch in Report277's threshold-free
argument for Corollary 5.8; the phase-localization branch is separate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem exists_good_progression_sample {N L : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hL : 2 ≤ L) (hN : L ^ 3 ≤ N)
    (hd : 0 < density A) (hd1 : density A < 1) :
    ∃ a d : ZMod N, d ∉ badProgressionDirections N L ∧
      density A + (1 - density A) / (2 * L) ≤ progressionSampleDensity A L a d := by
  classical
  have hL0 : 0 < L := by omega
  have hLr : (0 : Real) < L := by exact_mod_cast hL0
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let t : Real := (1 - density A) * density A * N
  let g : Real := t / (2 * L)
  let v : ZMod N → Real := fun d =>
    ∑ a, (progressionSampleDensity A L a d - density A) ^ 2
  have ht : 0 < t := mul_pos (mul_pos (sub_pos.mpr hd1) hd) hNr
  have hg : 0 ≤ g := by positivity
  have hhalf : 2 * L * g = t := by
    dsimp [g]
    field_simp
  by_contra hno
  have hsmall (a d : ZMod N) (hgood : d ∉ badProgressionDirections N L) :
      progressionSampleDensity A L a d ≤ density A + (1 - density A) / (2 * L) := by
    exact le_of_lt (lt_of_not_ge fun hx => hno ⟨a, d, hgood, hx⟩)
  have hupper (d : ZMod N) :
      v d ≤ g + if d ∈ badProgressionDirections N L then t else 0 := by
    by_cases hbad : d ∈ badProgressionDirections N L
    · rw [if_pos hbad]
      have hu : v d ≤ t := progressionSampleDensity_variance_upper A hL0 d 1
        (fun a => (progressionSampleDensity_range A hL0 a d).2)
      linarith
    · rw [if_neg hbad, add_zero]
      have hu := progressionSampleDensity_variance_upper A hL0 d
        (density A + (1 - density A) / (2 * L)) (fun a => hsmall a d hbad)
      have heq : (density A + (1 - density A) / (2 * L) - density A) * density A * N = g := by
        dsimp [g, t]
        ring
      exact heq ▸ hu
  have hsum : (∑ d, v d) ≤ (N : Real) * g + (badProgressionDirections N L).card * t := by
    calc
      _ ≤ ∑ d, (g + if d ∈ badProgressionDirections N L then t else 0) :=
        Finset.sum_le_sum fun d _ => hupper d
      _ = _ := by simp [Finset.sum_add_distrib]
  have hlower : (N : Real) * t ≤ L * ∑ d, v d := by
    have hv := progressionSampleDensity_variance_lower A hL0
    dsimp [t, v]
    nlinarith [hv]
  have hstrict : 2 * (L : Real) * (∑ d, v d) < 2 * ((N : Real) * t) := by
    calc
      _ ≤ 2 * L * ((N : Real) * g + (badProgressionDirections N L).card * t) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : Real) * t + (2 * L * (badProgressionDirections N L).card) * t := by
        nlinarith [congrArg (fun x : Real => (N : Real) * x) hhalf]
      _ < (N : Real) * t + (N : Real) * t := by
        linarith [mul_lt_mul_of_pos_right (badProgressionDirections_scaled_card_lt hL hN) ht]
      _ = 2 * ((N : Real) * t) := by ring
  nlinarith [hlower, hstrict]

theorem sum_realSetIndicator_on {N : Nat} [NeZero N] (A B : Finset (ZMod N)) :
    (∑ x ∈ B, realSetIndicator A x) = ((A ∩ B).card : Real) := by
  classical
  simp [realSetIndicator, Finset.inter_comm]

theorem progressionSampleDensity_eq_density_of_good {N L : Nat} [NeZero N]
    (A : Finset (ZMod N)) (a d : ZMod N)
    (hd : d ∉ badProgressionDirections N L) :
    progressionSampleDensity A L a d =
      ((A ∩ (ModAP.mk a d L).carrier).card : Real) / L := by
  classical
  have hinj : Function.Injective (fun i : Fin L => a + (i.val : ZMod N) * d) := by
    intro i j hij
    exact progression_direction_injective d hd (add_left_cancel hij)
  have hsum : (∑ i : Fin L, realSetIndicator A (a + (i.val : ZMod N) * d)) =
      ∑ x ∈ (ModAP.mk a d L).carrier, realSetIndicator A x := by
    simp only [ModAP.carrier, Finset.sum_image (fun i _ j _ hij => hinj hij)]
  rw [progressionSampleDensity, hsum, sum_realSetIndicator_on]

/-- The arbitrary-modulus variance lemma from Report277. -/
theorem exists_proper_progression_density_increment {N L : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hL : 2 ≤ L) (hN : L ^ 3 ≤ N)
    (hd : 0 < density A) (hd1 : density A < 1) :
    ∃ Q : ModAP N, Q.IsProper ∧ Q.length = L ∧
      (density A + (1 - density A) / (2 * L)) * Q.carrier.card ≤ (A ∩ Q.carrier).card := by
  obtain ⟨a, d, hgood, hgain⟩ := exists_good_progression_sample A hL hN hd hd1
  have hproper := progression_proper_of_good_direction a d hgood
  refine ⟨ModAP.mk a d L, hproper, rfl, ?_⟩
  rw [show (ModAP.mk a d L).carrier.card = L from hproper]
  rw [progressionSampleDensity_eq_density_of_good A a d hgood] at hgain
  exact (le_div_iff₀ (by exact_mod_cast (show 0 < L by omega))).mp hgain

/-- The low-correlation branch obtains the stronger gain `alpha / 3`, with
no phase-partition or lower bound on the correlation parameter. -/
theorem exists_proper_progression_of_small_correlation {N L : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hL : 2 ≤ L) (hN : L ^ 3 ≤ N)
    (hd : 0 < density A) (hd1 : density A < 1) {alpha : Real}
    (ha : alpha ≤ 3 * (1 - density A) / (2 * L)) :
    ∃ Q : ModAP N, Q.IsProper ∧ Q.length = L ∧
      (density A + alpha / 3) * Q.carrier.card ≤ (A ∩ Q.carrier).card := by
  obtain ⟨Q, hproper, hlen, hgain⟩ :=
    exists_proper_progression_density_increment A hL hN hd hd1
  refine ⟨Q, hproper, hlen, le_trans ?_ hgain⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [mul_div_assoc] at ha
  linarith [ha]

end LeanProofs.GowersSzemeredi
