import FabiusFunction.FabiusLambertHigherExpansion
import FabiusFunction.FabiusLambertRates
import FabiusFunction.FabiusSharpLambertMain
import FabiusFunction.FabiusWikipediaMain

/-!
# Explicit corrected Wikipedia expansion on the dyadic logarithmic scale

The compact lower-Lambert saddle main is the cleanest rigorous form of the
small-argument asymptotic.  This module expands it into the elementary form
printed on Wikipedia, while retaining the centered periodic correction at its
exact lower-Lambert phase.  The fourth phase term from
`FabiusLambertHigherExpansion` is essential: a coarser phase expansion would
leave an error of order `log t / t`, rather than the stated `1/t`.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- The nonperiodic elementary main term on the real dyadic log scale. -/
noncomputable def dyadicRealWikipediaElementaryMain (t : ℝ) : ℝ :=
  -Real.log 2 / 2 * t ^ 2 - t * Real.log t +
    (1 + Real.log 2 / 2) * t - Real.log t ^ 2 / (2 * Real.log 2) +
      fabiusSharpAsymptoticConstant -
        Real.log t ^ 2 / (2 * (Real.log 2) ^ 2 * t)

/-- The corrected real dyadic main term, with its exact lower-Lambert phase. -/
noncomputable def dyadicRealCorrectedWikipediaMain (t : ℝ) : ℝ :=
  dyadicRealWikipediaElementaryMain t +
    negativeLaplacePsi (dyadicLambertPhase t)

private lemma sharpLambert_dyadic_sub_realMain_eq
    {t : ℝ} (ht : 0 < t)
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    fabiusSharpLambertMain ((2 : ℝ) ^ (-t)) -
        dyadicRealCorrectedWikipediaMain t =
      ((1 - Real.log t) - Real.log 2 * t) *
          dyadicLambertSecondRefinedRemainder t +
        (1 - Real.log t) *
          (Real.log t - Real.log t ^ 2 / 2) /
            ((Real.log 2) ^ 3 * t ^ 2) -
        Real.log 2 / 2 * dyadicLambertRemainder t ^ 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hfixed := dyadicLambertPhase_fixedPoint hsmall
  have hlog : Real.log (dyadicLambertPhase t) =
      Real.log t + Real.log 2 * dyadicLambertRemainder t := by
    unfold dyadicLambertRemainder
    field_simp [hL] at hfixed ⊢
    linarith
  unfold fabiusSharpLambertMain dyadicRealCorrectedWikipediaMain
  rw [fabiusLambertPhase_dyadic]
  dsimp
  rw [hlog]
  unfold dyadicRealWikipediaElementaryMain
  unfold dyadicLambertSecondRefinedRemainder dyadicLambertRemainder
  field_simp [hL, ht0]
  ring

private lemma inv_sq_isBigO_inv :
    (fun t : ℝ => t⁻¹ ^ 2) =O[atTop] (fun t : ℝ => t⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
    abs_of_pos (inv_pos.mpr (zero_lt_one.trans_le ht)), one_mul]
  have hi0 : 0 ≤ t⁻¹ := (inv_pos.mpr (zero_lt_one.trans_le ht)).le
  have hi1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  nlinarith

private lemma log_pow_mul_inv_sq_isBigO_inv (k : ℕ) :
    (fun t : ℝ => Real.log t ^ k * t⁻¹ ^ 2) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := k)).isBigO.mul
    (isBigO_refl (fun t : ℝ => t⁻¹ ^ 2) atTop)
  apply h.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    simp only [id_eq]
    field_simp

private lemma multiplier_isBigO_id :
    (fun t : ℝ => (1 - Real.log t) - Real.log 2 * t) =O[atTop]
      (fun t : ℝ => t) := by
  have hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] (fun t : ℝ => t) :=
    (isLittleO_const_id_atTop (1 : ℝ)).isBigO
  have hlog : Real.log =O[atTop] (fun t : ℝ => t) :=
    Real.isLittleO_log_id_atTop.isBigO
  have hlinear := (isBigO_refl (fun t : ℝ => t) atTop).const_mul_left (Real.log 2)
  exact (hone.sub hlog).sub hlinear

private lemma secondRefined_mul_multiplier_isBigO_inv :
    (fun t : ℝ => ((1 - Real.log t) - Real.log 2 * t) *
      dyadicLambertSecondRefinedRemainder t) =O[atTop]
        (fun t : ℝ => t⁻¹) := by
  have h := multiplier_isBigO_id.mul dyadicLambertSecondRefinedRemainder_isBigO
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

private lemma explicit_second_order_term_isBigO_inv :
    (fun t : ℝ =>
      (1 - Real.log t) * (Real.log t - Real.log t ^ 2 / 2) /
        ((Real.log 2) ^ 3 * t ^ 2)) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
  have h1 := log_pow_mul_inv_sq_isBigO_inv 1
  have h2 := log_pow_mul_inv_sq_isBigO_inv 2
  have h3 := log_pow_mul_inv_sq_isBigO_inv 3
  have hsum := h1.add (h2.const_mul_left (-(3 / 2 : ℝ))) |>.add
    (h3.const_mul_left (1 / 2 : ℝ))
  have hscaled := hsum.const_mul_left ((Real.log 2) ^ 3)⁻¹
  apply hscaled.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hL]
  ring

private lemma lambertRemainder_sq_isBigO_inv :
    (fun t : ℝ => dyadicLambertRemainder t ^ 2) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
  let A : ℝ → ℝ := fun t => Real.log t / (Real.log 2) ^ 2 / t
  let E : ℝ → ℝ := dyadicLambertRefinedRemainder
  have hA : A =O[atTop] (fun t : ℝ => Real.log t * t⁻¹) := by
    have h := (isBigO_refl (fun t : ℝ => Real.log t * t⁻¹) atTop).const_mul_left
      ((Real.log 2) ^ 2)⁻¹
    apply h.congr' _ Filter.EventuallyEq.rfl
    filter_upwards with t
    dsimp [A]
    ring
  have hE : E =O[atTop] (fun t : ℝ => t⁻¹) := by
    apply dyadicLambertRefinedRemainder_isBigO.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    simp [one_div]
  have hlog2 : (fun t : ℝ => (Real.log t * t⁻¹) ^ 2) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
    apply (log_pow_mul_inv_sq_isBigO_inv 2).congr_left
    intro t
    ring
  have hA2 := (hA.pow 2).trans hlog2
  have hlog1 : (fun t : ℝ => (Real.log t * t⁻¹) * t⁻¹) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
    apply (log_pow_mul_inv_sq_isBigO_inv 1).congr_left
    intro t
    ring
  have hAE := (hA.mul hE).trans hlog1
  have hE2 := hE.pow 2 |>.trans inv_sq_isBigO_inv
  have hsum := hA2.add (hAE.const_mul_left 2) |>.add hE2
  apply hsum.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with t
  dsimp [A, E]
  unfold dyadicLambertRefinedRemainder
  ring

/-- The compact Lambert-coordinate saddle main has the explicit corrected
Wikipedia expansion on the real dyadic logarithmic scale, with error `O(1/t)`. -/
theorem fabiusSharpLambertMain_dyadic_sub_realWikipediaMain_isBigO :
    (fun t : ℝ => fabiusSharpLambertMain ((2 : ℝ) ^ (-t)) -
      dyadicRealCorrectedWikipediaMain t) =O[atTop]
        (fun t : ℝ => t⁻¹) := by
  have hsum := secondRefined_mul_multiplier_isBigO_inv.add
    explicit_second_order_term_isBigO_inv |>.sub
      (lambertRemainder_sq_isBigO_inv.const_mul_left (Real.log 2 / 2))
  apply hsum.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_dyadicLambertPhase_domain] with t ht hsmall
    exact (sharpLambert_dyadic_sub_realMain_eq ht hsmall).symm
  · exact Filter.EventuallyEq.rfl

/-- The elementary, nonperiodic expression in the Wikipedia small-argument
display, including its Euler--Stieltjes constant exactly as printed. -/
noncomputable def fabiusWikipediaElementaryMain (x : ℝ) : ℝ :=
  let lx := Real.log x;
  let llx := Real.log (-lx);
  let llog2 := Real.log (Real.log 2);
  -lx ^ 2 / (2 * Real.log 2) + lx * llx / Real.log 2 -
      (1 / 2 + (1 + llog2) / Real.log 2) * lx -
    llx ^ 2 / (2 * Real.log 2) + llog2 * llx / Real.log 2 +
    ((6 * Real.eulerMascheroniConstant ^ 2 + 12 * firstStieltjesConstant -
        Real.pi ^ 2 - 6 * llog2 ^ 2) / (12 * Real.log 2) -
      7 * Real.log 2 / 12 - Real.log Real.pi / 2) +
    llx ^ 2 / (2 * Real.log 2 * lx) -
      llog2 * llx / (Real.log 2 * lx)

/-- The corrected literal Wikipedia main: the printed elementary expression
plus the centered periodic term at the exact lower-Lambert phase. -/
noncomputable def fabiusExplicitCorrectedWikipediaMain (x : ℝ) : ℝ :=
  fabiusWikipediaElementaryMain x +
    negativeLaplacePsi (fabiusLambertPhase x)

/-- Substitution `x = 2⁻ᵗ` in the literal Wikipedia expression.  The
last two source terms leave the explicit `O(1/t)` difference shown here from
the source's separately displayed dyadic expression. -/
theorem fabiusWikipediaElementaryMain_dyadic_eq {t : ℝ} (ht : 0 < t) :
    fabiusWikipediaElementaryMain ((2 : ℝ) ^ (-t)) =
      dyadicRealWikipediaElementaryMain t +
        Real.log (Real.log 2) ^ 2 / (2 * (Real.log 2) ^ 2 * t) := by
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≠ 0 := hLpos.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hlogx : Real.log ((2 : ℝ) ^ (-t)) = -t * Real.log 2 := by
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hneglogx : -Real.log ((2 : ℝ) ^ (-t)) = Real.log 2 * t := by
    rw [hlogx]
    ring
  have hlogneg : Real.log (-Real.log ((2 : ℝ) ^ (-t))) =
      Real.log (Real.log 2) + Real.log t := by
    rw [hneglogx, Real.log_mul hL ht0]
  unfold fabiusWikipediaElementaryMain dyadicRealWikipediaElementaryMain
  dsimp
  rw [hlogneg, hlogx]
  unfold fabiusSharpAsymptoticConstant gammaZetaConstant
  field_simp [hL, ht0]
  ring

/-- The corrected literal and dyadic Wikipedia main terms differ by the same
explicit `O(1/t)` source-conversion term. -/
theorem fabiusExplicitCorrectedWikipediaMain_dyadic_eq {t : ℝ} (ht : 0 < t) :
    fabiusExplicitCorrectedWikipediaMain ((2 : ℝ) ^ (-t)) =
      dyadicRealCorrectedWikipediaMain t +
        Real.log (Real.log 2) ^ 2 / (2 * (Real.log 2) ^ 2 * t) := by
  unfold fabiusExplicitCorrectedWikipediaMain dyadicRealCorrectedWikipediaMain
  rw [fabiusWikipediaElementaryMain_dyadic_eq ht]
  rw [fabiusLambertPhase_dyadic]
  ring

/-- On the dyadic logarithmic scale, the compact corrected main differs from
the literal corrected Wikipedia expression by `O(1/t)`. -/
theorem fabiusCorrectedWikipediaMain_dyadic_sub_explicit_isBigO :
    (fun t : ℝ => fabiusCorrectedWikipediaMain ((2 : ℝ) ^ (-t)) -
      fabiusExplicitCorrectedWikipediaMain ((2 : ℝ) ^ (-t))) =O[atTop]
        (fun t : ℝ => t⁻¹) := by
  have hconversion :
      (fun t : ℝ => -(Real.log (Real.log 2) ^ 2 /
          (2 * (Real.log 2) ^ 2)) * t⁻¹) =O[atTop]
        (fun t : ℝ => t⁻¹) :=
    (isBigO_refl (fun t : ℝ => t⁻¹) atTop).const_mul_left _
  have hsum := fabiusSharpLambertMain_dyadic_sub_realWikipediaMain_isBigO.add
    hconversion
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_dyadicLambertPhase_domain] with t ht hsmall
  rw [fabiusCorrectedWikipediaMain_eq_sharpLambertMain
      (Real.rpow_pos_of_pos (by norm_num) _) hsmall,
    fabiusExplicitCorrectedWikipediaMain_dyadic_eq ht]
  field_simp [ht.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

/-- At `x → 0⁺`, the compact lower-Lambert main and the literal corrected
Wikipedia expression differ by the stated `O(1/(-log x))` rate. -/
theorem fabiusCorrectedWikipediaMain_sub_explicit_isBigO :
    (fun x : ℝ => fabiusCorrectedWikipediaMain x -
      fabiusExplicitCorrectedWikipediaMain x) =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹) := by
  let f : ℝ → ℝ := fun x => fabiusCorrectedWikipediaMain x -
    fabiusExplicitCorrectedWikipediaMain x
  have hlog : (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t : ℝ => (fabiusSmallArgumentLog (fabiusLogArgument t))⁻¹) := by
    apply fabiusCorrectedWikipediaMain_dyadic_sub_explicit_isBigO.congr'
    · filter_upwards with t
      rfl
    · filter_upwards with t
      rw [fabiusSmallArgumentLog_logArgument]
  have hs := isBigO_smallArgument_of_logScale f
    (fun x => (fabiusSmallArgumentLog x)⁻¹) hlog
  exact hs.trans (smallArgumentLog_inv_isBigO _)

end Fabius
