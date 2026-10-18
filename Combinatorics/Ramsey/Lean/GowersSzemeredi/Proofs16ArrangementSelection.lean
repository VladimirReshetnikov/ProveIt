import GowersSzemeredi.Proofs16InducedCounting

/-! # Selecting numerous, mostly respected fixed-side arrangements

`section16_good_sidelengths_with` takes the density `t1` as a parameter;
`section16_good_sidelengths_of_arrangements` is its printed instance.

`section16_good_sidelengths` and `section16_good_sidelengths_of_arrangements`
are in `Proofs16ArrangementSelectionSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Disintegrate a finite count over the fibres of any finite-valued map. -/
theorem countWhere_sum_fibres {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (P : X → Prop) :
    (∑ y : Y, countWhere (fun x => P x ∧ f x = y)) = countWhere P := by
  classical
  simp only [countWhere, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

theorem section16_sum_arrangementCountAtSide {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    (∑ h : Point N k, section16ArrangementCountAtSide d B h) =
      generalArrangementCount d B :=
  countWhere_sum_fibres GeneralArrangement.side (fun R => R.IsIn B)

theorem section16_sum_respectedArrangementCountAtSide {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (∑ h : Point N k, section16RespectedArrangementCountAtSide d B phi h) =
      respectedGeneralArrangementCount d B phi := by
  unfold section16RespectedArrangementCountAtSide respectedGeneralArrangementCount
  simpa only [and_assoc, and_left_comm, and_comm] using
    countWhere_sum_fibres GeneralArrangement.side (fun R => R.IsIn B ∧ R.IsRespected phi)

/-- Simultaneously discard fibres with excessive relative error and those
below an absolute mass threshold. -/
theorem weighted_good_large_mass {X : Type*} [Fintype X]
    (C G : X → Real) (eta t : Real) (heta : 0 < eta) (ht : 0 ≤ t)
    (hGC : ∀ x, G x ≤ C x)
    (hrespect : (1 - eta) * ∑ x, C x ≤ ∑ x, G x) :
    (∑ x, C x) / 2 - Fintype.card X * t ≤
      ∑ x, if (1 - 2 * eta) * C x ≤ G x ∧ t ≤ C x then C x else 0 := by
  have hpoint (x : X) : 2 * eta * C x ≤
      2 * eta * ((if (1 - 2 * eta) * C x ≤ G x ∧ t ≤ C x then C x else 0) + t) +
        (C x - G x) := by
    by_cases hg : (1 - 2 * eta) * C x ≤ G x
    · by_cases hc : t ≤ C x
      · simp only [hg, hc, and_self, ite_true]
        nlinarith [hGC x, mul_nonneg heta.le ht]
      · simp only [hg, hc, and_false, ite_false, zero_add]
        nlinarith [hGC x, mul_nonneg heta.le (sub_nonneg.mpr (le_of_not_ge hc))]
    · simp only [hg, false_and, ite_false, zero_add]
      nlinarith [mul_nonneg heta.le ht]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

theorem section16_good_sidelengths_with {N k : Nat} [NeZero N]
    (t1 : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht1 : 0 ≤ t1)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      t1 / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        t1 / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 := by
  let eta : Real := (2 : Real) ^ (-(44 : Real))
  let t : Real := t1 / 4 * (N : Real) ^ (16 * k + 15)
  let C (h : Point N k) : Real := section16ArrangementCountAtSide 8 B h
  let G (h : Point N k) : Real := section16RespectedArrangementCountAtSide 8 B phi h
  let H := Finset.univ.filter fun h => (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h
  have hC : (∑ h, C h) = generalArrangementCount 8 B := by
    simp only [C, ← Nat.cast_sum, section16_sum_arrangementCountAtSide]
  have hG : (∑ h, G h) = respectedGeneralArrangementCount 8 B phi := by
    simp only [G, ← Nat.cast_sum, section16_sum_respectedArrangementCountAtSide]
  have hGC (h : Point N k) : G h ≤ C h := Nat.cast_le.mpr (Finset.card_le_card fun R hR => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢; exact ⟨hR.1, hR.2.1⟩)
  have hmass := weighted_good_large_mass C G eta t (by positivity) (by positivity) hGC
    (by rw [hC, hG]; exact hB.2)
  have hbudget : (Fintype.card (Point N k) : Real) * t = t1 / 4 * (N : Real) ^ (17 * k + 15) := by
    rw [show Fintype.card (Point N k) = N ^ k by simp [Point, ZMod.card]]
    dsimp only [t]; push_cast; ring
  refine ⟨H, ?_, fun h hh => ?_⟩
  · change _ ≤ ∑ h ∈ H, C h
    simp only [H, Finset.sum_filter]
    linarith [hB.1]
  · have hgood : (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h := by simpa [H] using hh
    have he : 2 * eta = (2 : Real) ^ (-(43 : Real)) := by norm_num [eta, Real.rpow_neg]
    exact ⟨hgood.2, section16_domainApproxHomOfOrder_of_arrangementCounts B h phi _ (he ▸ hgood.1)⟩

end LeanProofs.GowersSzemeredi
