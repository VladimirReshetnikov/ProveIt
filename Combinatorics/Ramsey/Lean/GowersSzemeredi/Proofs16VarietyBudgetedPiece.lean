import GowersSzemeredi.Proofs16ExplicitConstantBounds
import GowersSzemeredi.Proofs16VarietyShapeMatch
import GowersSzemeredi.Proofs16VarietyPieceBudget
import GowersSzemeredi.Proofs16VarietyLossBound
import GowersSzemeredi.Proofs16VarietyScaleBounds
import GowersSzemeredi.Proofs16BudgetedExtraction
import GowersSzemeredi.Proofs16CorollaryLowDimensions

/-! The variety route's pieces at the source's piece budget.

At the named constants, every relation piece of the variety route
(`polynomialVarietyRelationPieceAt_explicit`) is `MultiplyLinear γ s` with the
explicit parameter
`s = section16VarietyThreeParameter D θ γ = 18r/γ + 64 + L`. Here `r` is the
Lemma 16.9 scale and `L` is the larger of the two logarithmic losses of the
ceiling-free controls (`MultiplyLinearWith.variety_three_multiplyLinear`).

The width coefficient, the count and the losses are written with the exact
arguments of `section16VarietyThreeCeilingFreeExponent`, so the shape
equalities of `Proofs16VarietyShapeMatch` apply by unfolding. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The variety count of the dimension-three pieces. -/
def section16VarietyThreeCount (D : Nat) (theta gamma : Real) : Nat :=
  section16VarietyExtractionCount D gamma (theta / 4)

/-- The `ρ`-free width coefficient of the dimension-three pieces. -/
def section16VarietyThreeWidthCoeff (D : Nat) (theta gamma : Real) : Real :=
  section16VarietyCeilingFreeWidthCoeff explicitLiftK explicitLiftP explicitVarietyK
    explicitVarietyP D (section16VarietyExtractionCount D gamma (theta / 4))
    (9 * section16VarietySpectrumCount D (theta / 2) gamma)
    (section16VarietyExtractionDensity gamma (theta / 4)) theta gamma
    (section16PolynomialJointVarietyExponent explicitVarietyK explicitVarietyP
      (section16VarietySpectrumCount D (theta / 2) gamma) D
      (section16VarietySpectrumDensity (theta / 2) gamma))

/-- The logarithmic loss of the dimension-three pieces. -/
def section16VarietyThreeLoss (D : Nat) (theta gamma : Real) : Real :=
  max (Real.log (section16VarietyThreeWidthCoeff D theta gamma)⁻¹)
    (Real.log (81 * 7 ^ 4 * ((section16VarietyThreeCount D theta gamma : Nat) : Real) ^ 2 + 27))

/-- The piece parameter of the dimension-three pieces. -/
def section16VarietyThreeParameter (D : Nat) (theta gamma : Real) : Real :=
  18 * section16Lemma9R (theta / 2) gamma 2 / gamma + 64 + section16VarietyThreeLoss D theta gamma

theorem section16VarietyThreeLoss_nonneg (D : Nat) (theta gamma : Real) :
    0 ≤ section16VarietyThreeLoss D theta gamma := by
  unfold section16VarietyThreeLoss
  refine le_trans (Real.log_nonneg ?_) (le_max_right _ _)
  have : (0 : Real) ≤ 81 * 7 ^ 4 * ((section16VarietyThreeCount D theta gamma : Nat) : Real) ^ 2 :=
    by positivity
  linarith

/-- The Lemma 16.9 scale is at least one. -/
theorem one_le_section16Lemma9R_half_two {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) : 1 ≤ section16Lemma9R (theta / 2) gamma 2 := by
  rw [section16Lemma9R_half_two_eq ht hg]
  have hx := two_le_two_div ht ht1 hg hg1
  have hgi : 1 ≤ gamma⁻¹ := (one_le_inv₀ hg).mpr hg1
  generalize 2 / (theta * gamma) = x at hx ⊢
  have h1 : (1 : Real) ≤ (32 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :=
    one_le_pow₀ (by linarith)
  have h2 : (1 : Real) ≤ gamma⁻¹ ^ 2 := one_le_pow₀ hgi
  calc (1 : Real) ≤ 3 * 1 * 1 := by norm_num
    _ ≤ 3 * gamma⁻¹ ^ 2 * (32 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (by norm_num) (by positivity)

/-- **Variety pieces are the source's multiple multilinearity at the explicit parameter.** -/
theorem MultiplyLinearWith.variety_three_multiplyLinear {N D : Nat} [NeZero N]
    {theta gamma : Real} {Piece : Finset (Point N 3 × ZMod N)}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hW : 0 < section16VarietyThreeWidthCoeff D theta gamma)
    (h : MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
      (section16VarietyThreePieceExponent explicitLiftK explicitLiftP explicitVarietyK
        explicitVarietyP explicitVarietyK explicitVarietyP D theta gamma) Piece) :
    MultiplyLinear gamma (section16VarietyThreeParameter D theta gamma) Piece := by
  have hcf := h.variety_three_ceiling_free two_le_explicitLiftK explicitLiftP_pos
    two_le_explicitVarietyK explicitVarietyP_pos two_le_explicitVarietyK explicitVarietyP_pos
    ht ht1 hg hg1
  have hr := one_le_section16Lemma9R_half_two ht ht1 hg hg1
  have hr0 : 0 < section16Lemma9R (theta / 2) gamma 2 := by linarith
  unfold section16VarietyThreeParameter
  refine hcf.multiplyLinear_of_variety_shape (k := 3)
    (Q := ((section16VarietyThreeCount D theta gamma : Nat) : Real))
    hg hg1 hr hW (Nat.cast_nonneg _) (section16VarietyThreeLoss_nonneg D theta gamma)
    (le_max_left _ _) (le_max_right _ _) ?_ ?_
  · intro rho hrho _
    unfold section16VarietyThreeCeilingFreeExponent
    rw [section16VarietyCeilingFreeExponent_eq_shape _ _ _ _ _ _ _ hr0 hrho hg]
    rfl
  · intro rho hrho _
    unfold section16VarietyThreeCeilingFreeGraphBound
    rw [section16VarietyCeilingFreeGraphBound_eq_shape _ hr0 hrho hg]
    rfl

/-- `y ≤ e^y`. -/
theorem le_exp_self (y : Real) : y ≤ Real.exp y := by
  have := Real.add_one_le_exp y; linarith

/-- `log y ≤ y` for `y > 0`. -/
theorem log_le_self_of_pos {y : Real} (hy : 0 < y) : Real.log y ≤ y := by
  have := Real.log_le_sub_one_of_pos hy; linarith

/-- **A count `⌈fam·e^mb⌉ + 1`, plus one, is at most `e^(fam + 3 + mb)`.** -/
theorem count_succ_le_exp {fam mb : Real} (hf : 0 ≤ fam) (hm : 0 ≤ mb) :
    (((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1 ≤ Real.exp (fam + 3 + mb) := by
  have hlog := log_extraction_count_le hf hm
  have hpos : 0 < (((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1 := by positivity
  have h3 := log_le_self_of_pos (show 0 < fam + 3 by linarith)
  calc _ = Real.exp (Real.log ((((Nat.ceil (fam * Real.exp mb) + 1 : Nat)) : Real) + 1)) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (fam + 3 + mb) := Real.exp_le_exp.mpr (by linarith)

/-- **Milićević's bound is a power of `x` when `4/c` is.** -/
theorem milicevicBound_le_pow {D K : Nat} {c x : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (h4 : 4 / c ≤ x ^ K) : milicevicBound D c ≤ x ^ (K * D) := by
  rw [pow_mul]
  exact (milicevicBound_le hc hc1).trans (pow_le_pow_left₀ (by positivity) h4 D)

/-- **The Bohr-radius term lies between `1` and `16 + 4·(5 + log m + S)`.** -/
theorem lg_bounds {m : Nat} (hm : 1 ≤ m) {S : Real} (hS : 0 ≤ S) :
    1 ≤ 16 + 4 * Real.log (16 / ((2 : Real) ^ (-S) / (4 * (m : Real)))) ∧
      16 + 4 * Real.log (16 / ((2 : Real) ^ (-S) / (4 * (m : Real)))) ≤
        16 + 4 * (5 + Real.log m + S) := by
  have hm0 : (1 : Real) ≤ m := by exact_mod_cast hm
  have h2S : 0 < (2 : Real) ^ (-S) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : 16 / ((2 : Real) ^ (-S) / (4 * (m : Real))) = 64 * (m : Real) * (2 : Real) ^ S := by
    rw [Real.rpow_neg (by norm_num)]
    field_simp
    ring
  rw [heq]
  have h2S' : 1 ≤ (2 : Real) ^ S := Real.one_le_rpow (by norm_num) hS
  have hlog : Real.log (64 * (m : Real) * (2 : Real) ^ S) = Real.log 64 + Real.log m + S * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by norm_num)]
  have hl64 : Real.log 64 ≤ 5 := by
    rw [show (64 : Real) = 2 ^ 6 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm0
  have hl64' : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  constructor
  · rw [hlog]; nlinarith
  · rw [hlog]
    have : S * Real.log 2 ≤ S := by nlinarith
    linarith

theorem nine_le_exp_three : (9 : Real) ≤ Real.exp 3 := by
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  calc (9 : Real) ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3

/-- **The loss of the dimension-three pieces fits the budget.** -/
theorem section16VarietyThreeLoss_le {D : Nat} {theta gamma : Real} (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hD : D ≤ 2 ^ 64)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700) :
    0 < section16VarietyThreeWidthCoeff D theta gamma ∧
      section16VarietyThreeLoss D theta gamma ≤
        (2 / (theta * gamma)) ^ (64 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by
  obtain ⟨hK, hP, hVK, hVP⟩ := hconst
  obtain ⟨hc1, hc11⟩ := section16VarietyExtractionDensity_pos_le_one gamma
    (show 0 < theta / 4 by positivity) (by linarith)
  obtain ⟨hc2, hc21⟩ := section16VarietySpectrumDensity_pos_le_one
    (show 0 < theta / 2 by positivity) (by linarith) hg hg1
  have hS0 : 0 ≤ multipleS (theta / 2) gamma 2 :=
    le_trans zero_le_one (one_le_multipleS 2 (by positivity) (by linarith) hg hg1)
  -- the two counts
  have hm1 : 0 ≤ milicevicBound D (section16VarietyExtractionDensity gamma (theta / 4)) :=
    pow_nonneg (by linarith [two_le_milicevic_base hc1 hc11]) D
  have hm2 : 0 ≤ milicevicBound D (section16VarietySpectrumDensity (theta / 2) gamma) :=
    pow_nonneg (by linarith [two_le_milicevic_base hc2 hc21]) D
  have hQ : ((section16VarietyExtractionCount D gamma (theta / 4) : Nat) : Real) + 1 ≤
      Real.exp ((section16VarietyExtractionFamily gamma (theta / 4) : Real) + 3 +
        milicevicBound D (section16VarietyExtractionDensity gamma (theta / 4))) := by
    unfold section16VarietyExtractionCount
    exact count_succ_le_exp (Nat.cast_nonneg _) hm1
  have hn : ((section16VarietySpectrumCount D (theta / 2) gamma : Nat) : Real) + 1 ≤
      Real.exp ((section16VarietyExtractionFamily
          (section16Delta (section16ThetaOne (theta / 2) gamma 2))
          (section16ThetaOne (theta / 2) gamma 2 / 8) : Real) + 3 +
        milicevicBound D (section16VarietySpectrumDensity (theta / 2) gamma)) := by
    unfold section16VarietySpectrumCount section16VarietyExtractionCount
    exact count_succ_le_exp (Nat.cast_nonneg _) hm2
  -- the Bohr-radius term
  have hm : 1 ≤ explicitLiftK * (9 * section16VarietySpectrumCount D (theta / 2) gamma + 1) :=
    Nat.mul_pos (by have := two_le_explicitLiftK; omega) (by omega)
  obtain ⟨hLg1, hLgle⟩ := lg_bounds hm hS0
  -- the power bounds, all in `x = 2/(θγ)`
  have hF1 : (section16VarietyExtractionFamily gamma (theta / 4) : Real) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 26) := variety_family_le ht ht1 hg hg1
  have hd1 := variety_density_inv_le ht ht1 hg hg1
  have hF2 : (section16VarietyExtractionFamily (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8) : Real) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 157) := spectrum_family_le ht ht1 hg hg1
  have hd2 := spectrum_density_inv_le ht ht1 hg hg1
  have hSx := multipleS_half_two_le ht ht1 hg hg1
  have hx := two_le_two_div ht ht1 hg hg1
  have hmb1 := milicevicBound_le_pow (D := D) hc1 hc11 hd1
  have hmb2 := milicevicBound_le_pow (D := D) hc2 hc21 hd2
  clear hd1 hd2
  have hF10 : (0 : Real) ≤ (section16VarietyExtractionFamily gamma (theta / 4) : Real) :=
    Nat.cast_nonneg _
  have hF20 : (0 : Real) ≤ (section16VarietyExtractionFamily
      (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8) : Real) := Nat.cast_nonneg _
  unfold section16VarietyThreeLoss section16VarietyThreeWidthCoeff section16VarietyCeilingFreeWidthCoeff
    section16PolynomialJointVarietyExponent section16Zeta section16VarietyThreeCount
  -- name every quantity; after this no hypothesis has a non-atomic big-power base
  generalize (section16VarietyExtractionFamily gamma (theta / 4) : Real) = F1 at hQ hF1 hF10 ⊢
  generalize (section16VarietyExtractionFamily (section16Delta (section16ThetaOne (theta / 2) gamma 2))
    (section16ThetaOne (theta / 2) gamma 2 / 8) : Real) = F2 at hn hF2 hF20 ⊢
  generalize milicevicBound D (section16VarietyExtractionDensity gamma (theta / 4)) = m1
    at hQ hm1 hmb1 ⊢
  generalize milicevicBound D (section16VarietySpectrumDensity (theta / 2) gamma) = m2
    at hn hm2 hmb2 ⊢
  generalize multipleS (theta / 2) gamma 2 = S at hS0 hLg1 hLgle hSx ⊢
  generalize 2 / (theta * gamma) = x at hF1 hF2 hmb1 hmb2 hSx hx ⊢
  generalize section16VarietySpectrumCount D (theta / 2) gamma = n at hn hm hLg1 hLgle ⊢
  generalize section16VarietyExtractionCount D gamma (theta / 4) = Q at hQ ⊢
  generalize (16 + 4 * Real.log (16 / ((2 : Real) ^ (-S) /
    (4 * ((explicitLiftK * (9 * n + 1) : Nat) : Real))))) = Lg at hLg1 hLgle ⊢
  -- `2^1700` as an atom
  obtain ⟨B, hBdef⟩ : ∃ B, (2 : Real) ^ 1700 = B := ⟨_, rfl⟩
  have hB8 : (8 : Real) ≤ B := by
    rw [← hBdef]
    exact le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) (by norm_num : 3 ≤ 1700))
  have hx1 : (1 : Real) ≤ x := le_trans (by norm_num) hx
  have hBx : B ≤ x ^ 1700 := by rw [← hBdef]; exact pow_le_pow_left₀ (by norm_num) hx 1700
  rw [hBdef] at hK hP hVK hVP
  clear hBdef
  -- logarithmic facts
  have hn1 : Real.log ((n : Real) + 1) ≤ F2 + 3 + m2 := by
    have := Real.log_le_log (by positivity) hn
    rwa [Real.log_exp] at this
  have hlog9 : Real.log 9 ≤ 3 := by
    have := Real.log_le_log (by norm_num) nine_le_exp_three
    rwa [Real.log_exp] at this
  have hK0 : (0 : Real) < explicitLiftK := by
    have := two_le_explicitLiftK
    exact_mod_cast (show 0 < explicitLiftK by omega)
  have hlogm : Real.log ((explicitLiftK * (9 * n + 1) : Nat) : Real) ≤ B + 3 + (F2 + 3 + m2) := by
    push_cast
    rw [Real.log_mul hK0.ne' (by positivity)]
    have h1 : Real.log (explicitLiftK : Real) ≤ B := (log_le_self_of_pos hK0).trans hK
    have h2 : Real.log (9 * (n : Real) + 1) ≤ Real.log 9 + Real.log ((n : Real) + 1) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg n : (0 : Real) ≤ n)])
    linarith
  -- the master bound
  have hLgΛ : Lg ≤ 16 + 4 * (5 + (B + 3 + (F2 + 3 + m2)) + S) := by linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Real, 7 + 8 * B + (F1 + 3 + m1) + (F2 + 6 + m2) + Lg = Λ := ⟨_, rfl⟩
  have hΛ7 : 7 ≤ Λ := by rw [← hΛdef]; linarith
  have hle : ∀ y : Real, y ≤ Λ → y ≤ Real.exp Λ := fun y hy => hy.trans (le_exp_self Λ)
  have hexp3 : Real.exp (F2 + 6 + m2) ≤ Real.exp Λ :=
    Real.exp_le_exp.mpr (by rw [← hΛdef]; linarith)
  have hqΛ : ((9 * n : Nat) : Real) + 1 ≤ Real.exp Λ := by
    calc ((9 * n : Nat) : Real) + 1 ≤ Real.exp 3 * ((n : Real) + 1) := by
          push_cast; nlinarith [nine_le_exp_three, (Nat.cast_nonneg n : (0 : Real) ≤ n)]
      _ ≤ Real.exp 3 * Real.exp (F2 + 3 + m2) :=
          mul_le_mul_of_nonneg_left hn (Real.exp_pos 3).le
      _ = Real.exp (F2 + 6 + m2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp Λ := hexp3
  have hP1 : (1 : Real) ≤ explicitLiftP := by exact_mod_cast explicitLiftP_pos
  have hVP1 : (1 : Real) ≤ explicitVarietyP := by exact_mod_cast explicitVarietyP_pos
  obtain ⟨hWpos, hlogW, hlogQ⟩ := variety_loss_le (p := (explicitLiftP : Real))
    (q := ((9 * n : Nat) : Real)) (pv := (explicitVarietyP : Real))
    (Cv := (explicitVarietyK : Real)) (mb := m1) (Q := (Q : Real)) (Lg := Lg)
    (ps := (explicitVarietyP : Real)) (Cs := (explicitVarietyK : Real)) (n := (n : Real))
    (mb' := m2) (Λ := Λ) hΛ7
    hP1 (hle _ (by rw [← hΛdef]; linarith)) (Nat.cast_nonneg _) hqΛ
    hVP1 (hle _ (by rw [← hΛdef]; linarith)) (Nat.cast_nonneg _)
    (hle _ (by rw [← hΛdef]; linarith))
    hm1 (hle _ (by rw [← hΛdef]; linarith)) (Nat.cast_nonneg _)
    (hQ.trans (Real.exp_le_exp.mpr (by rw [← hΛdef]; linarith)))
    hLg1 (hle _ (by rw [← hΛdef]; linarith)) hVP1 (hle _ (by rw [← hΛdef]; linarith))
    (Nat.cast_nonneg _) (hle _ (by rw [← hΛdef]; linarith)) (Nat.cast_nonneg _)
    (hn.trans (Real.exp_le_exp.mpr (by rw [← hΛdef]; linarith))) hm2
    (hle _ (by rw [← hΛdef]; linarith))
  -- `112·Λ ≤ x^(64·2^256)`
  have hE : ∀ k : Nat, k ≤ 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) →
      x ^ k ≤ x ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := fun k hk => pow_le_pow_right₀ hx1 hk
  have hD1 : 2 ^ 27 * D ≤ 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) :=
    (Nat.mul_le_mul_left _ hD).trans (by norm_num)
  have hD2 : 2 ^ 158 * D ≤ 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) :=
    (Nat.mul_le_mul_left _ hD).trans (by norm_num)
  have hB' := hBx.trans (hE 1700 (by norm_num))
  have hF1' := hF1.trans (hE _ (by norm_num))
  have hF2' := hF2.trans (hE _ (by norm_num))
  have hm1' := hmb1.trans (hE _ hD1)
  have hm2' := hmb2.trans (hE _ hD2)
  have h14 : (16384 : Real) ≤ x ^ 14 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 14)
  have htop : x ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) * x ^ 14 ≤
      x ^ (64 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hx1 (by norm_num)
  clear hF1 hF2 hmb1 hmb2 hBx hE
  generalize x ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) = X at hB' hF1' hF2' hm1' hm2' hSx htop
  generalize x ^ (64 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) = Z at htop ⊢
  generalize x ^ 14 = Y at h14 htop
  have hX1 : 1 ≤ X := le_trans (by linarith) hB'
  have hΛX : Λ ≤ 104 * X := by rw [← hΛdef]; linarith
  have hfin : 112 * Λ ≤ Z := by
    calc 112 * Λ ≤ 112 * (104 * X) := by linarith
      _ ≤ 16384 * X := by linarith
      _ ≤ Y * X := mul_le_mul_of_nonneg_right h14 (by linarith)
      _ = X * Y := by ring
      _ ≤ Z := htop
  exact ⟨hWpos, max_le (hlogW.trans hfin) (hlogQ.trans hfin)⟩


/-- **The source's piece budget in dimension three, from deep variety structure.**
The named constants enter only through their bounds `hconst`. -/
theorem section16_budgeted_piece_three_of_deep_of_constants {D : Nat} (hD : D ≤ 2 ^ 64)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700)
    (hM : MilicevicDeepVarietyStructure D) : Section16BudgetedPieceAt 3 := by
  intro gamma theta hg hg1 ht ht1
  -- `1 ≤ s`, before any big-power hypothesis is in scope
  have hs1 : 1 ≤ section16VarietyThreeParameter D theta gamma := by
    unfold section16VarietyThreeParameter
    have hL0 := section16VarietyThreeLoss_nonneg D theta gamma
    have hr := one_le_section16Lemma9R_half_two ht ht1 hg hg1
    have : 0 ≤ 18 * section16Lemma9R (theta / 2) gamma 2 / gamma :=
      div_nonneg (by linarith) hg.le
    linarith
  obtain ⟨hWpos, hL⟩ := section16VarietyThreeLoss_le ht ht1 hg hg1 hD hconst
  have hs := variety_piece_budget ht ht1 hg hg1 hL
  clear hL
  refine ⟨section16VarietyPieceMass theta gamma, section16VarietyThreeParameter D theta gamma,
    section16VarietyPieceMass_pos ht hg, hs1, hs, ?_⟩
  obtain ⟨N0, hN0⟩ := polynomialVarietyRelationPieceAt_explicit D hM theta gamma ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN Gamma _ hprod hlarge => ?_⟩
  obtain ⟨Piece, hPiece, hmass, hML⟩ := hN0 N hN Gamma hprod hlarge
  exact ⟨Piece, hPiece, hmass, hML.variety_three_multiplyLinear ht ht1 hg hg1 hWpos⟩

/-- **Theorem 16.2 in dimension three, from deep variety structure.** -/
theorem theorem_16_2_at_three_of_deep_of_constants {D : Nat} (hD : D ≤ 2 ^ 64)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700)
    (hM : MilicevicDeepVarietyStructure D) : Theorem162At 3 :=
  theorem_16_2_of_budgeted_piece (section16_budgeted_piece_three_of_deep_of_constants hD hconst hM)

/-- **Corollary 16.11 in dimension three, from deep variety structure.** -/
theorem corollary_16_11_at_three_of_deep_of_constants {D : Nat} (hD : D ≤ 2 ^ 64)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700)
    (hM : MilicevicDeepVarietyStructure D) : Corollary1611At 3 :=
  Theorem162At.corollary_16_11 (by norm_num)
    (theorem_16_2_at_three_of_deep_of_constants hD hconst hM)

end LeanProofs.GowersSzemeredi
