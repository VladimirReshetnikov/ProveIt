/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Estimates.FiniteProductWeightL1
import OAI.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def coefficientCRTEquiv {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (J → ZMod (∏ l, q l)) ≃+ (∀ l, J → ZMod (q l)) where
  toFun x l j := ZMod.prodEquivPi q hq (x j) l
  invFun y j := (ZMod.prodEquivPi q hq).symm (fun l => y l j)
  left_inv x := by funext j; exact (ZMod.prodEquivPi q hq).symm_apply_apply (x j)
  right_inv y := by
    funext l j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l j)) l
  map_add' x y := by
    funext l j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x j) (y j)) l

theorem coefficientCRTEquiv_apply {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : J → ZMod (∏ l, q l)) (l : L) (j : J) :
    coefficientCRTEquiv q hq x l j =
      ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l)) (x j) :=
  ZMod.prodEquivPi_apply q hq (x j) l

theorem coefficientCRTEquiv_intCast {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k))) (z : J → ℤ) :
    coefficientCRTEquiv q hq (fun j => (z j : ZMod (∏ l, q l))) =
      (fun l j => (z j : ZMod (q l))) := by
  funext l j
  rw [coefficientCRTEquiv_apply, map_intCast]

private theorem uniform_map_equiv {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (e : X ≃ Y) :
    (PMF.uniformOfFintype X).map e = PMF.uniformOfFintype Y := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [pmf_map_injective_at _ _ e.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem dependentProductPMF_uniform {L : Type*} [Fintype L] {X : L → Type*}
    [∀ l, Fintype (X l)] [∀ l, Nonempty (X l)]
    [∀ l, MeasurableSpace (X l)] [∀ l, MeasurableSingletonClass (X l)] :
    dependentProductPMF (fun l => PMF.uniformOfFintype (X l)) =
      PMF.uniformOfFintype (∀ l, X l) := by
  ext x
  simp only [dependentProductPMF_apply, PMF.uniformOfFintype_apply,
    Fintype.card_pi, Nat.cast_prod]
  exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm

theorem uniform_coefficientCRT_map {L J : Type*} [Fintype L] [Fintype J]
    (q : L → ℕ) [∀ l, NeZero (q l)] [NeZero (∏ l, q l)]
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (PMF.uniformOfFintype (J → ZMod (∏ l, q l))).map (coefficientCRTEquiv q hq) =
      dependentProductPMF (fun l => PMF.uniformOfFintype (J → ZMod (q l))) := by
  rw [dependentProductPMF_uniform]
  exact uniform_map_equiv (coefficientCRTEquiv q hq).toEquiv

theorem selectedPrimePower_coprime (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    Pairwise (fun p q : S => (p.val ^ a p).Coprime (q.val ^ a q)) := by
  intro p q hpq
  exact Nat.coprime_pow_primes _ _ (hprime p p.property) (hprime q q.property)
    (fun h => hpq (Subtype.ext h))

theorem selectedPrimePower_nonzero (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∀ p : S, p.val ^ a p ≠ 0) ∧ (∏ p : S, p.val ^ a p) ≠ 0 := by
  have hp (p : S) : p.val ^ a p ≠ 0 := pow_ne_zero _ (hprime p p.property).ne_zero
  exact ⟨hp, Finset.prod_ne_zero_iff.mpr (fun p _ => hp p)⟩

theorem uniform_selectedPrimePowerCRT_map (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (J : Type*) [Fintype J] :
    let : ∀ p : S, NeZero (p.val ^ a p) := fun p =>
      ⟨(selectedPrimePower_nonzero S a hprime).1 p⟩
    let : NeZero (∏ p : S, p.val ^ a p) := ⟨(selectedPrimePower_nonzero S a hprime).2⟩
    (PMF.uniformOfFintype (J → ZMod (∏ p : S, p.val ^ a p))).map
        (coefficientCRTEquiv (fun p : S => p.val ^ a p) (selectedPrimePower_coprime S a hprime)) =
      dependentProductPMF (fun p : S => PMF.uniformOfFintype (J → ZMod (p.val ^ a p))) := by
  let : ∀ p : S, NeZero (p.val ^ a p) := fun p =>
    ⟨(selectedPrimePower_nonzero S a hprime).1 p⟩
  let : NeZero (∏ p : S, p.val ^ a p) := ⟨(selectedPrimePower_nonzero S a hprime).2⟩
  exact uniform_coefficientCRT_map _ _

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothCoefficientPMF_residue_apply (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M] (r : ZMod M) :
    ((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal =
      shiftedSmoothSampleSum ((a - r.val) / M) (S / M) / shiftedSmoothSampleSum a S := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hinj : Function.Injective (fun k : ℤ => (r.val : ℤ) + M * k) := by
    intro j k h
    exact mul_left_cancel₀ hM (add_left_cancel h)
  rw [pmf_map_toReal_indicator]
  have he := hinj.tsum_eq (f := fun z : ℤ =>
      (shiftedSmoothCoefficientPMF a S hS hZ z).toReal *
        (if (z : ZMod M) = r then 1 else 0)) (by
    intro z hz
    have hz' : (z : ZMod M) = r := by
      by_contra hn
      simp only [Function.mem_support, hn, ite_false, mul_zero, ne_eq, not_true_eq_false] at hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff M z r).mp hz'
    exact ⟨k, hk.symm⟩)
  rw [← he]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero, ZMod.natCast_zmod_val, ite_true, mul_one,
    shiftedSmoothCoefficientPMF_apply]
  rw [tsum_div_const]
  congr 1
  unfold shiftedSmoothSampleSum
  apply tsum_congr
  intro k
  congr 1
  field_simp
  ring

theorem shiftedSmoothSampleSum_sub_width_abs_le (a : ℝ) {S : ℝ} (hS : 1 ≤ S) :
    |shiftedSmoothSampleSum a S - S| ≤ 4 * (probabilityProfileLipschitz : ℝ) := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he := shiftedSmoothSampleSum_error a hS
  have he' : |shiftedSmoothSampleSum a S - S| / S ≤
      4 * (probabilityProfileLipschitz : ℝ) / S := by
    calc
      _ = |(shiftedSmoothSampleSum a S - S) / S| := by rw [abs_div, abs_of_pos hS0]
      _ = |shiftedSmoothSampleSum a S / S - 1| := by rw [sub_div, div_self hS0.ne']
      _ ≤ _ := he
  exact (div_le_div_iff_of_pos_right hS0).mp he'

theorem shiftedSmoothCoefficientPMF_residue_error (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M]
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S) (r : ZMod M) :
    |((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal -
      1 / (M : ℝ)| ≤ 16 * (probabilityProfileLipschitz : ℝ) / S := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hM : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hL1 : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hL : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  have hbase : 8 * (probabilityProfileLipschitz : ℝ) ≤ S := by
    have := mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 8 * (probabilityProfileLipschitz : ℝ) by positivity)
    nlinarith only [this, hlarge]
  have hSM : 1 ≤ S / M := by
    apply (le_div_iff₀ hM).mpr
    nlinarith only [hlarge, mul_le_mul_of_nonneg_right hL1 hM.le]
  have hmain := shiftedSmoothSampleSum_sub_width_abs_le a (show 1 ≤ S by linarith)
  have hprog := shiftedSmoothSampleSum_sub_width_abs_le ((a - r.val) / M) hSM
  have hmainDiv : |S / M - shiftedSmoothSampleSum a S / M| ≤
      4 * (probabilityProfileLipschitz : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hM, abs_sub_comm]
    exact (div_le_iff₀ hM).mpr (hmain.trans (by nlinarith only [mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 4 * (probabilityProfileLipschitz : ℝ) by positivity)]))
  have hnum : |shiftedSmoothSampleSum ((a - r.val) / M) (S / M) -
      shiftedSmoothSampleSum a S / M| ≤ 8 * (probabilityProfileLipschitz : ℝ) := by
    have h := abs_sub_le (shiftedSmoothSampleSum ((a - r.val) / M) (S / M))
      (S / M) (shiftedSmoothSampleSum a S / M)
    linarith
  rw [shiftedSmoothCoefficientPMF_residue_apply]
  have heq : shiftedSmoothSampleSum ((a - r.val) / M) (S / M) / shiftedSmoothSampleSum a S -
      1 / (M : ℝ) =
      (shiftedSmoothSampleSum ((a - r.val) / M) (S / M) - shiftedSmoothSampleSum a S / M) /
        shiftedSmoothSampleSum a S := by field_simp
  rw [heq, abs_div, abs_of_pos hZ]
  apply (div_le_iff₀ hZ).mpr
  apply hnum.trans
  have hlo := (shiftedSmoothSampleSum_bounds a hbase).1
  calc
    _ = (16 * (probabilityProfileLipschitz : ℝ) / S) * (S / 2) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

theorem shiftedSmoothCoefficientPMF_residue_l1 (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M]
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S) :
    (∑ r : ZMod M,
      |((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal -
        1 / (M : ℝ)|) ≤ 16 * (probabilityProfileLipschitz : ℝ) * M / S := by
  calc
    _ ≤ ∑ _r : ZMod M, 16 * (probabilityProfileLipschitz : ℝ) / S :=
      Finset.sum_le_sum (fun r _ => shiftedSmoothCoefficientPMF_residue_error a S hS hZ M hlarge r)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

noncomputable def smoothCoefficientResidueWeights (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M] :
    FiniteProbabilityWeights (ZMod M) :=
  ofPMF ((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)))

theorem smoothCoefficientProduct_residue_event_error {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : ∀ j, 0 < shiftedSmoothSampleSum (a j) (S j))
    (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (E : (J → ZMod M) → Prop) :
    |(pi (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j) (hZ j) M)).eventProbability E -
      (uniform (J → ZMod M)).eventProbability E| ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  have h := abs_eventProbability_pi_sub_le_sum
    (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j) (hZ j) M)
    (fun _ : J => uniform (ZMod M)) E
  have hu : (pi (fun _ : J => uniform (ZMod M))).eventProbability E =
      (uniform (J → ZMod M)).eventProbability E := by
    unfold eventProbability mean
    apply Finset.sum_congr rfl
    intro x _
    rw [pi_uniform_weight]
  rw [hu] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [smoothCoefficientResidueWeights, ofPMF_weight, uniform, ZMod.card, one_div] using
    shiftedSmoothCoefficientPMF_residue_l1 (a j) (S j) (hS j) (hZ j) M (hlarge j)

theorem smoothCoefficientProduct_residue_event_error_of_width {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : ∀ j, 0 < shiftedSmoothSampleSum (a j) (S j))
    {B W η : ℝ} (hB : 0 ≤ B) (hW : 0 < W)
    (hwidth : ∀ j, W ≤ S j)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * B ≤ W)
    (herror : (Fintype.card J : ℝ) * (16 * (probabilityProfileLipschitz : ℝ) * B / W) ≤ η)
    (M : ℕ) [NeZero M] (hM : (M : ℝ) ≤ B)
    (E : (J → ZMod M) → Prop) :
    |(pi (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j) (hZ j) M)).eventProbability E -
      (uniform (J → ZMod M)).eventProbability E| ≤ η := by
  have hscale (j) : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j :=
    ((mul_le_mul_of_nonneg_left hM (by positivity)).trans hlarge).trans (hwidth j)
  apply (smoothCoefficientProduct_residue_event_error a S hS hZ M hscale E).trans
  calc
    _ ≤ ∑ _j : J, 16 * (probabilityProfileLipschitz : ℝ) * B / W := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hM (by positivity))
        hW (hwidth j)
    _ ≤ η := by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror

theorem shiftedSmoothProductPMF_residue_weight {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (r : J → ZMod M) :
    (ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).weight r =
    (pi (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ j) M)).weight r := by
  rw [ofPMF_weight, shiftedSmoothProductPMF_eq_independent]
  change ((dependentProductPMF _).map _ r).toReal = _
  rw [dependentProductPMF_map, dependentProductPMF_apply, ENNReal.toReal_prod]
  rfl

theorem shiftedSmoothProductPMF_residue_event_error {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (E : (J → ZMod M) → Prop) :
    |(ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).eventProbability E -
      (uniform (J → ZMod M)).eventProbability E| ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  have h := smoothCoefficientProduct_residue_event_error a S hS
    (shiftedSmoothProductMass_coordinate_pos a S hS hZ) M hlarge E
  simpa only [eventProbability, mean, shiftedSmoothProductPMF_residue_weight] using h

theorem shiftedSmoothProductPMF_residue_l1 {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j) :
    (∑ r, |(ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).weight r -
      (uniform (J → ZMod M)).weight r|) ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  let hz := shiftedSmoothProductMass_coordinate_pos a S hS hZ
  have h := pi_weight_l1_le_sum
    (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j) (hz j) M)
    (fun _ : J => uniform (ZMod M))
  simp only [pi_uniform_weight] at h
  simp only [shiftedSmoothProductPMF_residue_weight]
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [smoothCoefficientResidueWeights, ofPMF_weight, uniform, ZMod.card, one_div] using
    shiftedSmoothCoefficientPMF_residue_l1 (a j) (S j) (hS j) (hz j) M (hlarge j)

theorem shiftedSmoothProductPMF_residue_complexMean_error {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (f : (J → ZMod M) → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖(ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).complexMean f -
      (uniform (J → ZMod M)).complexMean f‖ ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j :=
  (norm_complexMean_sub_le_weight_l1 _ _ f hf).trans
    (shiftedSmoothProductPMF_residue_l1 a S hS hZ M hlarge)

theorem shiftedSmoothProductPMF_residue_transfer {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (w : FiniteProbabilityWeights (J → ZMod M)) (E : (J → ZMod M) → Prop)
    {ε K : ℝ}
    (hcompare : w.eventProbability E ≤
      (ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
        (fun x j => (x j : ZMod M)))).eventProbability E + ε)
    (huniform : (uniform (J → ZMod M)).eventProbability E ≤ K) :
    w.eventProbability E ≤ K + ε +
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  have h := (abs_le.mp (shiftedSmoothProductPMF_residue_event_error a S hS hZ M hlarge E)).2
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem shiftedSmoothProductFiniteWeights_residue_complexMean_error
    {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (f : (J → ZMod M) → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖(shiftedSmoothProductFiniteWeights a S hS hZ).complexMean
        (fun x => f (fun j => (x.val j : ZMod M))) -
      (uniform (J → ZMod M)).complexMean f‖ ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [shiftedSmoothProductFiniteWeights_map_complexMean a S hS hZ
    (fun x j => (x j : ZMod M)) f]
  exact shiftedSmoothProductPMF_residue_complexMean_error a S hS hZ M hlarge f hf

theorem shiftedSmoothProductFiniteWeights_residue_event_error
    {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (E : (J → ZMod M) → Prop) :
    |(shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability
        (fun x => E (fun j => (x.val j : ZMod M))) -
      (uniform (J → ZMod M)).eventProbability E| ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [shiftedSmoothProductFiniteWeights_map_event a S hS hZ
    (fun x j => (x j : ZMod M)) E]
  exact shiftedSmoothProductPMF_residue_event_error a S hS hZ M hlarge E

private theorem residue_error_sum_le_of_width {J : Type*} [Fintype J]
    (S : J → ℝ) {B W η : ℝ} (hB : 0 ≤ B) (hW : 0 < W)
    (hwidth : ∀ j, W ≤ S j)
    (herror : (Fintype.card J : ℝ) *
      (16 * (probabilityProfileLipschitz : ℝ) * B / W) ≤ η)
    (M : ℕ) (hM : (M : ℝ) ≤ B) :
    (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j) ≤ η := by
  calc
    _ ≤ ∑ _j : J, 16 * (probabilityProfileLipschitz : ℝ) * B / W := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hM (by positivity))
        hW (hwidth j)
    _ ≤ η := by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror

theorem shiftedSmoothProductFiniteWeights_residue_complexMean_error_of_width
    {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S)
    {B W η : ℝ} (hB : 0 ≤ B) (hW : 0 < W)
    (hwidth : ∀ j, W ≤ S j)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * B ≤ W)
    (herror : (Fintype.card J : ℝ) *
      (16 * (probabilityProfileLipschitz : ℝ) * B / W) ≤ η)
    (M : ℕ) [NeZero M] (hM : (M : ℝ) ≤ B)
    (f : (J → ZMod M) → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖(shiftedSmoothProductFiniteWeights a S hS hZ).complexMean
        (fun x => f (fun j => (x.val j : ZMod M))) -
      (uniform (J → ZMod M)).complexMean f‖ ≤ η := by
  have hscale (j) : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j :=
    ((mul_le_mul_of_nonneg_left hM (by positivity)).trans hlarge).trans (hwidth j)
  exact (shiftedSmoothProductFiniteWeights_residue_complexMean_error a S hS hZ M hscale f hf).trans
    (residue_error_sum_le_of_width S hB hW hwidth herror M hM)

theorem shiftedSmoothProductFiniteWeights_residue_event_error_of_width
    {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S)
    {B W η : ℝ} (hB : 0 ≤ B) (hW : 0 < W)
    (hwidth : ∀ j, W ≤ S j)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * B ≤ W)
    (herror : (Fintype.card J : ℝ) *
      (16 * (probabilityProfileLipschitz : ℝ) * B / W) ≤ η)
    (M : ℕ) [NeZero M] (hM : (M : ℝ) ≤ B)
    (E : (J → ZMod M) → Prop) :
    |(shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability
        (fun x => E (fun j => (x.val j : ZMod M))) -
      (uniform (J → ZMod M)).eventProbability E| ≤ η := by
  have hscale (j) : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j :=
    ((mul_le_mul_of_nonneg_left hM (by positivity)).trans hlarge).trans (hwidth j)
  exact (shiftedSmoothProductFiniteWeights_residue_event_error a S hS hZ M hscale E).trans
    (residue_error_sum_le_of_width S hB hW hwidth herror M hM)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem uniform_coefficientCRT_event {L J : Type*} [Fintype L] [Fintype J]
    (q : L → ℕ) [∀ l, NeZero (q l)] [NeZero (∏ l, q l)]
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (E : ∀ l, (J → ZMod (q l)) → Prop) :
    (uniform (J → ZMod (∏ l, q l))).eventProbability
        (fun y => ∀ l, E l (coefficientCRTEquiv q hq y l)) =
      ∏ l, (uniform (J → ZMod (q l))).eventProbability (E l) := by
  have h := uniform_mean_surjective_hom (coefficientCRTEquiv q hq).toAddMonoidHom
    (coefficientCRTEquiv q hq).surjective
    (fun y => @ite ℝ (∀ l, E l (y l)) (Classical.propDecidable _) 1 0)
  have hevent : (uniform (J → ZMod (∏ l, q l))).eventProbability
      (fun y => ∀ l, E l (coefficientCRTEquiv q hq y l)) =
      (uniform (∀ l, J → ZMod (q l))).eventProbability (fun y => ∀ l, E l (y l)) := by
    simp only [eventProbability, AddEquiv.coe_toAddMonoidHom] at h ⊢
    convert h using 1
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    congr 1
  rw [hevent]
  have hpi : (uniform (∀ l, J → ZMod (q l))).eventProbability (fun y => ∀ l, E l (y l)) =
      (pi (fun l => uniform (J → ZMod (q l)))).eventProbability (fun y => ∀ l, E l (y l)) := by
    unfold eventProbability mean
    apply Finset.sum_congr rfl
    intro y _
    rw [pi_uniform_weight]
  rw [hpi, eventProbability_pi]

theorem shiftedSmoothProductFiniteWeights_primePower_event
    {J : Type*} [Fintype J] (center width : J → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (S : Finset ℕ) (a : ℕ → ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    [∀ p : S, NeZero (p.val ^ a p)]
    (E : ∀ p : S, (J → ZMod (p.val ^ a p)) → Prop)
    (hprob : ∀ p : S, (uniform (J → ZMod (p.val ^ a p))).eventProbability (E p) ≤
      1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) ≤ width j) :
    (shiftedSmoothProductFiniteWeights center width hwidth hZ).eventProbability
        (fun x => ∀ p : S, E p (fun j => (x.val j : ZMod (p.val ^ a p)))) ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) / width j := by
  let : NeZero (∏ p : S, p.val ^ a p) := ⟨(selectedPrimePower_nonzero S a hprime).2⟩
  let q : S → ℕ := fun p => p.val ^ a p
  let hq := selectedPrimePower_coprime S a hprime
  let F : (J → ZMod (∏ p : S, q p)) → Prop :=
    fun y => ∀ p : S, E p (coefficientCRTEquiv q hq y p)
  have htransfer := shiftedSmoothProductPMF_residue_event_error
    center width hwidth hZ (∏ p : S, q p) hlarge F
  have hactual := shiftedSmoothProductFiniteWeights_map_event center width hwidth hZ
    (fun x j => (x j : ZMod (∏ p : S, q p))) F
  have hF (x : J → ℤ) : F (fun j => (x j : ZMod (∏ p : S, q p))) =
      (∀ p : S, E p (fun j => (x j : ZMod (p.val ^ a p)))) := by
    simp only [F, coefficientCRTEquiv_intCast, q]
  simp only [hF] at hactual
  rw [← hactual] at htransfer
  have huniform : (uniform (J → ZMod (∏ p : S, q p))).eventProbability F ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 := by
    rw [uniform_coefficientCRT_event q hq E]
    calc
      _ ≤ ∏ p : S, 1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10 :=
    Finset.prod_le_prod₀ (fun p _ => (uniform _).eventProbability_nonneg (E p)) (fun p _ => hprob p)
      _ = _ := by
        simp only [one_div, ← Finset.prod_inv_distrib, ← Finset.prod_pow, Nat.cast_prod]
  have hupper := (abs_le.mp htransfer).2
  dsimp only [q] at hupper huniform
  linarith only [hupper, huniform]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

def smoothResiduePrimeBad {J : Type*} (P : Finset ℕ)
    (E : ∀ p : P, ∀ a : ℕ, (J → ZMod (p.val ^ a)) → Prop)
    (p a : ℕ) (x : J → ℤ) : Prop :=
  ∃ hp : p ∈ P, E ⟨p, hp⟩ a (fun j => (x j : ZMod (p ^ a)))

theorem smoothResidue_badPrimeProduct_probability {J : Type*} [Fintype J]
    (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
    (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (E : ∀ p : P, ∀ a : ℕ, (J → ZMod (p.val ^ a)) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ P, p ^ A p ≤ Q)
    (hprob : ∀ (p : P) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
      (uniform (J → ZMod (p.val ^ a))).eventProbability (E p a) ≤
        1 / ((p.val ^ a : ℕ) : ℝ) ^ 10)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (max Q (R ^ 2) : ℕ) / width j) ≤ η) :
    (shiftedSmoothProductFiniteWeights center width hwidth hZ).eventProbability
      (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ P, p ^ largestTestedBadDepth A
          (fun p a x => smoothResiduePrimeBad P E p a x.val) p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  apply largestBadPrimeProduct_probability_bounded _ P A _ hprime hQs hQ hR hdepth hη
  intro T hTP a ha hd
  let (p : T) : NeZero (p.val ^ a p) := ⟨pow_ne_zero _ (hprime p (hTP p.property)).ne_zero⟩
  let F (p : T) := E ⟨p.val, hTP p.property⟩ (a p)
  have hprod : (∏ p : T, p.val ^ a p) = ∏ p ∈ T, p ^ a p :=
    Finset.prod_coe_sort T (fun p => p ^ a p)
  have hd' : (∏ p : T, p.val ^ a p) ≤ max Q (R ^ 2) := by
    rw [hprod]
    exact hd
  have hs (j) : 8 * (probabilityProfileLipschitz : ℝ) * (∏ p : T, p.val ^ a p) ≤ width j :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hd') (by positivity)).trans (hlarge j)
  have h := shiftedSmoothProductFiniteWeights_primePower_event center width hwidth hZ T a
    (fun p hp => hprime p (hTP hp)) F
    (fun p => hprob ⟨p.val, hTP p.property⟩ (a p) (ha p p.property).1
      (ha p p.property).2.1 (ha p p.property).2.2) hs
  have hevents : (fun x : rectangularWeightIndices center width 1 =>
      ∀ p ∈ T, smoothResiduePrimeBad P E p (a p) x.val) =
      (fun x => ∀ p : T, F p (fun j => (x.val j : ZMod (p.val ^ a p)))) := by
    funext x
    apply propext
    constructor
    · intro hx p
      obtain ⟨hp, he⟩ := hx p p.property
      exact he
    · intro hx p hp
      exact ⟨hTP hp, hx ⟨p, hp⟩⟩
  rw [hevents]
  have herr : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p) / width j) ≤ η := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) herror
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hd') (by positivity)) (hwidth j).le
  rw [hprod] at h herr
  exact h.trans (add_le_add le_rfl herr)

theorem exists_early_smoothResidue_badPrimeProduct_cutoff (Qs : ℕ) (hQs : 2 ≤ Qs)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (J : Type*) [Fintype J]
      (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
      (hZ : 0 < shiftedSmoothProductMass center width)
      (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
      (E : ∀ p : P, ∀ a : ℕ, (J → ZMod (p.val ^ a)) → Prop) (Q : ℕ),
      (∀ p ∈ P, p.Prime) → 1 ≤ Q → (∀ p ∈ P, p ^ A p ≤ Q) →
      (∀ (p : P) a, 0 < a → a ≤ A p → Qs ≤ p.val ^ a →
        (uniform (J → ZMod (p.val ^ a))).eventProbability (E p a) ≤
          1 / ((p.val ^ a : ℕ) : ℝ) ^ 10) →
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j) →
      (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) / width j) ≤
        δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) →
      (shiftedSmoothProductFiniteWeights center width hwidth hZ).eventProbability
        (fun x => smallPrimePowerCorrection Qs * R <
          ∏ p ∈ P, p ^ largestTestedBadDepth A
            (fun p a x => smoothResiduePrimeBad P E p a x.val) p x) ≤ δ := by
  obtain ⟨R, hR, hradius⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro J _ center width hwidth hZ P A _ E Q hprime hQ hdepth hprob hlarge herror
  exact (smoothResidue_badPrimeProduct_probability center width hwidth hZ P A E hprime hQs hQ hR
    hdepth hprob hlarge (hradius Q hQ).1.le herror).trans (hradius Q hQ).2

end Erdos3

end

end OAI
