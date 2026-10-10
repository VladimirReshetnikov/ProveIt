import GowersSzemeredi.Proofs16InducedCounting

/-! # Selecting numerous, mostly respected fixed-side arrangements -/
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
  classical
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

/-- The averaging part of Lemma 16.5, including the exact error parameter
required by Theorem 10.13. Only the arrangement conditions (ii) and (iii) of
Lemma 16.4 are used; the cross-section condition (i) is not. -/
theorem section16_good_sidelengths_of_arrangements {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (htheta : 0 < theta) (hgamma : 0 < gamma)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 := by
  classical
  let eta : Real := (2 : Real) ^ (-(44 : Real))
  let t : Real := section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15)
  let C (h : Point N k) : Real := section16ArrangementCountAtSide 8 B h
  let G (h : Point N k) : Real := section16RespectedArrangementCountAtSide 8 B phi h
  let H := Finset.univ.filter fun h => (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h
  have heta : 0 < eta := by dsimp [eta]; positivity
  have ht : 0 ≤ t := by dsimp [t, section16ThetaOne]; positivity
  have hC : (∑ h, C h) = generalArrangementCount 8 B := by
    dsimp [C]
    rw [← Nat.cast_sum, section16_sum_arrangementCountAtSide]
  have hG : (∑ h, G h) = respectedGeneralArrangementCount 8 B phi := by
    dsimp [G]
    rw [← Nat.cast_sum, section16_sum_respectedArrangementCountAtSide]
  have hGC (h : Point N k) : G h ≤ C h := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact ⟨hR.1, hR.2.1⟩
  have hrespect : (1 - eta) * ∑ h, C h ≤ ∑ h, G h := by
    rw [hC, hG]
    exact hB.2
  have hmass := weighted_good_large_mass C G eta t heta ht hGC hrespect
  have htotal : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤ ∑ h, C h := by
    rw [hC]
    exact hB.1
  have hcard : Fintype.card (Point N k) = N ^ k := by simp [Point, ZMod.card]
  have hbudget : (Fintype.card (Point N k) : Real) * t =
      section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) := by
    rw [hcard, Nat.cast_pow]
    dsimp [t]
    rw [show 17 * k + 15 = k + (16 * k + 15) by omega, pow_add]
    ring
  refine ⟨H, ?_, ?_⟩
  · change _ ≤ ∑ h ∈ H, C h
    simp only [H, Finset.sum_filter]
    rw [hbudget] at hmass
    linarith
  · intro h hh
    have hgood : (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h := by simpa [H] using hh
    refine ⟨hgood.2, section16_domainApproxHomOfOrder_of_arrangementCounts B h phi _ ?_⟩
    have he : 2 * eta = (2 : Real) ^ (-(43 : Real)) := by norm_num [eta, Real.rpow_neg]
    rw [← he]
    exact hgood.1

/-- The averaging part of Lemma 16.5 for a structured pair. -/
theorem section16_good_sidelengths {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (htheta : 0 < theta) (hgamma : 0 < gamma)
    (hB : Section16StructuredPair theta gamma B phi) :
    ∃ H : Finset (Point N k),
      section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 :=
  section16_good_sidelengths_of_arrangements theta gamma B phi htheta hgamma hB.2

end LeanProofs.GowersSzemeredi
