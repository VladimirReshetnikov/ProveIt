import GowersSzemeredi.Proofs16IntervalWordGeometry
import GowersSzemeredi.Proofs16SlabWordScales

/-! Balanced interval-alphabet words on short, positive-density slabs fail
the actual unit cover, while retaining the interval product-property budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exists_nonunit_interval_slabs (k : Nat) :
    ∃ R N₀ : Nat, 0 < R ∧
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∃ (L : Nat) (f : ZMod N → ZMod N),
          R ≤ N ∧ 0 < L ∧ L ≤ N ∧ 4 * L * R ≤ N ∧
          (1 / (8 * (R : Real))) * N ≤ L ∧
          (∀ x, f x ∈ (modInterval N 0 R).carrier) ∧
          ¬ MultiplyLinearFunction 1 1
            (lastProductSet (Finset.univ : Finset (Point N k)) (modInterval N 0 L).carrier)
            (fun z => f (section16Last z)) := by
  let delta := multipleC (1 / 2) 1 (k + 1)
  have hd : 0 < delta := by unfold delta multipleC; positivity
  have hd1 : delta ≤ 1 := by
    unfold delta multipleC
    exact pow_le_one₀ (by norm_num) (by norm_num)
  let K : Nat := Nat.ceil (multipleQ (1 / 2) 1 (k + 1))
  have hK : multipleQ (1 / 2) 1 (k + 1) ≤ (K : Real) := Nat.le_ceil _
  have hKpos : (0 : Real) < K := (inv_pos.mpr hd).trans_le hK
  have hKn : 0 < K := by exact_mod_cast hKpos
  let R := 4 * K
  have hR : 0 < R := by dsimp [R]; omega
  have hRpos : (0 : Real) < R := by exact_mod_cast hR
  let theta : Real := 1 / (8 * R)
  have ht : 0 < theta := by dsimp [theta]; positivity
  let epsilon : Real := 1 / (32 * K)
  have heps : 0 < epsilon := by dsimp [epsilon]; positivity
  let beta : Real := 1 / (R : Real) + epsilon
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hsmall : (K : Real) * beta ≤ 9 / 32 := by
    dsimp [beta, epsilon, R]
    push_cast
    apply le_of_eq
    field_simp
    ring
  have hdhalf : 0 < delta / 2 := by positivity
  obtain ⟨Nword, hword⟩ := exists_balanced_progression_word_large_N R hR
    hdhalf (by linarith : delta / 2 ≤ 1) heps
  let Tpower := positivePowerThreshold 1 (theta ^ delta) (delta / 2)
  let Twidth := positivePowerThreshold (32 * (K : Real) * R) 1 (delta / 2)
  refine ⟨R, max Nword (max (8 * R) (max (Nat.ceil Tpower) (Nat.ceil Twidth))), hR, ?_⟩
  intro N _ _ hN
  have hNword : Nword ≤ N := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNsize : 8 * R ≤ N := (le_max_left _ _).trans hrest
  have hthresholds := (le_max_right _ _).trans hrest
  have hNpower : Tpower ≤ N := (Nat.le_ceil Tpower).trans
    (by exact_mod_cast (le_max_left _ _).trans hthresholds)
  have hNwidth : Twidth ≤ N := (Nat.le_ceil Twidth).trans
    (by exact_mod_cast (le_max_right _ _).trans hthresholds)
  have hRN : R ≤ N := by omega
  obtain ⟨w, hw⟩ := hword N hNword
  let f : ZMod N → ZMod N := fun x => ((w x).val : ZMod N)
  obtain ⟨hf, hbal⟩ := balanced_word_cast_interval hRN w ((N : Real) ^ (delta / 2)) beta hbeta hw
  obtain ⟨hLpos, hLN, hprod, hmass⟩ := section16SlabLength_bounds hR hNsize
  let L := section16SlabLength N R
  refine ⟨L, f, hRN, hLpos, hLN, hprod, hmass, hf, ?_⟩
  apply balanced_word_not_multiplyLinear_on_box _ (alphabetIntervalBox N (k + 1) L)
    (alphabetIntervalBox_proper hLN) alphabetIntervalBox_subset_slab
    (alphabetIntervalBox_nonempty hLpos) (modInterval N 0 R).carrier f hf
    (K : Real) ((N : Real) ^ (delta / 2)) beta hbeta hK ?_ hbal hsmall ?_
  · rw [alphabetIntervalBox_width]
    exact section16_slab_power_scale ht hd hmass hNpower
  · have hcard : (modInterval N 0 R).carrier.card = R := modInterval_zero_isProper hRN
    rw [hcard]
    have hwidth : 32 * (K : Real) * R ≤ (N : Real) ^ (delta / 2) := by
      simpa only [one_mul] using positivePowerThreshold_spec (by norm_num : (0 : Real) < 1) hdhalf hNwidth
    linarith only [hwidth]

end LeanProofs.GowersSzemeredi
