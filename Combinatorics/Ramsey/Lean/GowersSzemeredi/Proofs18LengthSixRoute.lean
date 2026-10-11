import GowersSzemeredi.Proofs18SinglePieceInverse
import GowersSzemeredi.Proofs16PolyCoverTwo

/-! The degree-four inverse theorem from the polynomial recurrence alone.

`single_piece_quartic_inverse_global` turns `PolyCoverAt 1`, `PolyCoverAt 2`,
lift-width functions `C, W`, a retiled linearity bound and per-modulus
scale conditions into `FunctionDiscrepancyBound 4`. This module supplies
every input except the scale conditions:
* `sixQb`, `sixEb`: the controls of `polyCoverAt_one` at `l = 1` and of
  `polyCoverAt_two_of_family_lemma6` at `l = 2`;
* `sixC`, `sixW`: the minima of the two lift iterates;
* the retiled linearity bound in base dimension two, from the recurrence
  profile (`Section16RecurrenceProfileWith.retiled_family`).

The recurrence enters as two abstract profiles, in base dimensions one (for
`PolyCoverAt 2`) and two (for the retiling). The heavy bridge supplies them
with explicit constants (`multilinearPartitionBoundAt_explicit`).
* `length_six_quartic_inverse`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The count controls at `l = 1, 2`. -/
def sixQb (l : Nat) : Real → Real → Real → Real :=
  if l = 1 then fun gamma theta _ => ((3 * section16BaseFamilyBound gamma theta : Nat) : Real)
  else polyTwoQb

/-- The width-exponent controls at `l = 1, 2`. -/
def sixEb (A Bq : Nat → Real) (l : Nat) : Real → Real → Real → Real :=
  if l = 1 then fun gamma theta => cubicBaseExponent (section16BaseFamilyBound gamma theta)
  else polyTwoEb A Bq

theorem sixCov {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq)) :
    ∀ l, 1 ≤ l → l ≤ 2 → PolyCoverAt l (sixQb l) (sixEb A Bq l) := by
  intro l hl1 hl2
  interval_cases l
  · simp only [sixQb, sixEb]
    exact polyCoverAt_one
  · simp only [sixQb, sixEb, show (2 : Nat) ≠ 1 by decide, if_false]
    exact polyCoverAt_two_of_family_lemma6 hA hB hlemma6

theorem sixQb_ge_one (l : Nat) (g t s : Real) : 1 ≤ sixQb l g t s := by
  unfold sixQb
  split_ifs
  · have h := section16BaseFamilyBound_pos g t
    show (1 : Real) ≤ ((3 * section16BaseFamilyBound g t : Nat) : Real)
    exact_mod_cast (show 1 ≤ 3 * section16BaseFamilyBound g t by omega)
  · unfold polyTwoQb
    refine le_trans ?_ (le_max_right _ _)
    have h3 : (3 : Real) ≤ polyTwoThreshold t g := le_max_left _ _
    have hc : 1 ≤ ⌈polyTwoThreshold t g⌉₊ := by
      have : (1 : Real) ≤ ⌈polyTwoThreshold t g⌉₊ :=
        (by norm_num : (1 : Real) ≤ 3).trans (h3.trans (Nat.le_ceil _))
      exact_mod_cast this
    exact_mod_cast (show 1 ≤ 3 ^ 2 * ⌈polyTwoThreshold t g⌉₊ by
      have := Nat.mul_le_mul_left (3 ^ 2) hc
      omega)

theorem sixEb_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q) (l : Nat) (g t s : Real)
    (hs : 0 < s) (_hs1 : s ≤ 1) : 0 < sixEb A Bq l g t s := by
  unfold sixEb
  split_ifs
  · exact cubicBaseExponent_pos (section16BaseFamilyBound_pos g t) hs
  · exact section16CappedWidthExponent_pos (polyTwoFamExp_pos hB hs)

/-- The lift density functions, before iteration. -/
def sixBaseC (Qb : Nat → Real → Real → Real → Real) (alpha : Real) (l : Nat) : Real → Real :=
  fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2)

/-- The common lift density: the minimum of the two iterates. -/
def sixC (Qb : Nat → Real → Real → Real → Real) (alpha : Real) : Real → Real :=
  fun t => min ((liftLastC^[2] (sixBaseC Qb alpha 1)) t) ((liftLastC^[1] (sixBaseC Qb alpha 2)) t)

/-- The common lift width: the minimum of the two iterates. -/
def sixW (Eb : Nat → Real → Real → Real → Real) (alpha : Real) : Real → Nat → Nat :=
  fun t L => min ((liftLastW^[2] (coverWidth (Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2)))) t L)
    ((liftLastW^[1] (coverWidth (Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2)))) t L)

theorem sixBaseC_pos_le {Qb : Nat → Real → Real → Real → Real}
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s) (alpha : Real) (l : Nat) :
    ∀ s, 0 < s → s ≤ 1 → 0 < sixBaseC Qb alpha l s ∧ sixBaseC Qb alpha l s ≤ 1 := by
  intro s hs hs1
  have hq := hQb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2) (by positivity)
    (by linarith)
  unfold sixBaseC
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by linarith)]
  linarith

theorem sixC_pos_le {Qb : Nat → Real → Real → Real → Real}
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s) (alpha : Real) :
    ∀ t, 0 < t → t ≤ 1 → 0 < sixC Qb alpha t ∧ sixC Qb alpha t ≤ 1 := by
  intro t ht ht1
  obtain ⟨a1, a2⟩ := liftLastC_iterate_pos_le (sixBaseC_pos_le hQb alpha 1) 2 t ht ht1
  obtain ⟨b1, b2⟩ := liftLastC_iterate_pos_le (sixBaseC_pos_le hQb alpha 2) 1 t ht ht1
  exact ⟨lt_min a1 b1, (min_le_left _ _).trans a2⟩

theorem sixW_mono (Eb : Nat → Real → Real → Real → Real) (alpha : Real) :
    ∀ t, Monotone (sixW Eb alpha t) := by
  intro t L L' hLL'
  exact min_le_min (liftLastW_iterate_mono (coverWidth_mono _) 2 t hLL')
    (liftLastW_iterate_mono (coverWidth_mono _) 1 t hLL')

/-- **Degree-four inverse theorem from the recurrence profiles**, up to the
per-modulus scale conditions. -/
theorem length_six_quartic_inverse {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hK2 : 2 ≤ K2)
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2))
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {e : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) {Tloc : Real}
    (hmod : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      SinglePieceModulusConditions sixQb
        (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1))
        (sixC sixQb alpha)
        (sixW (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) alpha)
        alpha 2 (familyRecExp 2 p2) (familyRecThr 2 K2 p2) e N) :
    FunctionDiscrepancyBound 4 alpha
      (singlePieceEta sixQb (sixC sixQb alpha) alpha 2 *
        fejerCubicDiscrepancyParameter (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha) / 4)
      (inverseStepExponent (2 + 1) e
        (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) 16))
      (max (shortLocalizationThreshold (2 + 1) e (6 * ((2 + 1 : Nat) : Real))
          (fejerCubicInverseThreshold (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) Tloc)
        (inverseStepThreshold (2 + 1) (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)
          (fejerCubicDiscrepancyParameter (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) e
          (6 * ((2 + 1 : Nat) : Real))
          (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) 16))) := by
  have hA : ∀ q, 0 < familyWidthPrefactor K1 q := familyWidthPrefactor_pos (by omega)
  have hB : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  have hlemma6 := abstractFamilyLemma166At_of 1 hK1 hp1 hrec1
  have hretile : ∀ q, Section16RetiledLinearityBound 2 q (familyRecExp 2 p2 q) (familyRecThr 2 K2 p2 q) :=
    fun q => (hrec2.retiled_family (fun q => familyRecThr_pos (by omega) q) q).single
  refine single_piece_quartic_inverse_global ha haHalf (sixCov hA hB hlemma6)
    (fun l g t s _ _ => sixQb_ge_one l g t s)
    (fun l g t s hs hs1 => sixEb_pos hB l g t s hs hs1)
    (sixC_pos_le (fun l g t s _ _ => sixQb_ge_one l g t s) alpha)
    (sixW_mono _ alpha) ?_ ?_ _ _ hretile he0 he hmod
  · intro l hl1 hl2 t
    interval_cases l
    · exact min_le_left _ _
    · exact min_le_right _ _
  · intro l hl1 hl2 t L
    interval_cases l
    · exact min_le_left _ _
    · exact min_le_right _ _

end LeanProofs.GowersSzemeredi
