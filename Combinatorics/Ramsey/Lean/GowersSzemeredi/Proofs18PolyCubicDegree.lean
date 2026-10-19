import GowersSzemeredi.Proofs13PolySquareExtraction
import GowersSzemeredi.Proofs18FejerCubicAt
import GowersSzemeredi.Proofs18FejerReciprocalBudgets
import GowersSzemeredi.Proofs18EnvelopeBounds
import GowersSzemeredi.Proofs18TheoremOneDegrees

/-! **The polynomial degree-three base**, from a polynomial phase partition
(Notes L.7c, P10a).

`Theorem181At 3` asks for a discrepancy partition with parameter and
average-cell exponent at least `section18Exponent α 3 = α^(2^8192)`.
* The corpus parameter `fejerCubicDiscrepancyParameter α` is polynomial,
  `β⁻¹ ≤ (2/α)^(2^59)`.
* The corpus exponent is doubly exponential: its square exponent carries the
  catalogue row exponent `2^(−13Q)`.

The module supplies `PolyEnvBound`, its monotonicity, and
`polyEnvBound_three_of_phase_partition`. Its conversion to Theorem 18.1
(`theorem181At_of_polyEnvBound`) and the printed degree-three theorem, which
specializes this shared polynomial base, are in `Proofs18PolyCubicDegreeSide`.

The same chain is the degree-three base of the Theorem 18.2 envelope
(`envBound_three_of_phase_partition`, `EnvBound 3 62`). Its threshold is at
most the explicit `fejerCubicInverseThreshold α`
(`fejerCubicInverseThresholdAt_poly_le`): every threshold of the chain is a
positive-power threshold, antitone in its exponent, and the polynomial row
exponent is at least the catalogue's `2^(-13Q)`.

Here the square comes from `section13_complete_square_extraction_poly`, at
the density `δ = (α/2)^4207554485` of the corpus frequency graph
(`fejerSquareAt_poly`). The resulting σ satisfies `σ⁻¹ ≤ (2/α)^(2^74)`:
* the row exponent contributes `2^69`;
* the two square factors contribute `2^42` and `2^45`;
* the local count exponent contributes `2^59`.

The printed theorem (`theorem_18_1_three_of_phase_partition`, outside the
final route) takes the phase partition as a hypothesis. Its constants need
`K ≤ 2^p` and `p ≤ 2^(2^64)`; since `ProgressionPhasePartition.mono` raises
`p` freely, the explicit constants of `CommonDiffPartitionBoundAt 1` qualify
(bridge).

`section18Exponent_le_of_inv_le` is in `Proofs18PolyCubicDegreeSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The polynomial Fejér square.** The corpus frequency graph followed by
the polynomial Section 13 square extraction. -/
theorem fejerSquareAt_poly {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {K : Real} {p : Nat} (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    FejerSquareAt alpha (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat)))
      (max (section13FrequencyGraphThreshold alpha : Real)
        (section13PolyGeometricThreshold p ((alpha / 2) ^ (4207554485 : Nat)))) := by
  let delta := (alpha / 2) ^ (4207554485 : Nat)
  have hδ : 0 < delta := by positivity
  have hδone : delta ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hαone])
  intro N _ _ hN f hf hnot
  obtain ⟨A, psi, hA, hfreiman, hmostly, hfourier⟩ := section13_fejer_frequency_graph_explicit
    alpha hα hαone N (Nat.cast_le.mp ((le_max_left _ _).trans hN)) f hf hnot
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos (by exact_mod_cast NeZero.pos N) _
  have hδβ : delta ≤ A.card / (N : Real) ^ 2 := (le_div_iff₀ hN2).mpr hA
  have hcard : A.card ≤ N ^ 2 :=
    (Finset.card_le_univ A).trans_eq (by simp only [Pair, Fintype.card_prod, ZMod.card, sq])
  obtain ⟨P, Q, B, hPs, hPQ, hP, hQ, hlen, hsize, hBA, hbox, hmass, mu, hmu, hagree⟩ :=
    section13_complete_square_extraction_poly hδ hδone hpp hp hK hpB N
      ⟨A, psi, _, _, hδ.trans_le hδβ, (div_le_one hN2).mpr (by exact_mod_cast hcard),
        (div_mul_cancel₀ _ hN2.ne').symm, hfreiman, rfl, hmostly⟩
      hδβ ((le_max_right _ _).trans hN)
  refine ⟨P, Q, B, mu, hPs, hPQ, hP, hQ, hlen, hsize, hbox,
    le_trans (by gcongr; exact section13_fejer_square_density hα hαone) hmass,
    ⟨mu, hmu, fun _ _ => rfl⟩, fun z hz => ?_⟩
  rw [← hagree z hz]
  exact hfourier z (hBA hz)

/-! ### The envelope of the polynomial exponent -/

section Envelope

variable {X : Real}

theorem inv_mul_le_pw (hX : 2 ≤ X) {x y : Real} (hy : 0 < y) {a b : Nat}
    (h1 : x⁻¹ ≤ X ^ (2 ^ a)) (h2 : y⁻¹ ≤ X ^ (2 ^ b)) : (x * y)⁻¹ ≤ X ^ (2 ^ (max a b + 1)) := by
  rw [mul_inv]
  exact pw_mul' hX (inv_nonneg.mpr hy.le) h1 h2

/-- `section13Q δ ≤ X^(2^54)` once `δ⁻¹ ≤ X^(2^32)`. -/
theorem section13Q_le_pw (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) : section13Q delta ≤ X ^ (2 ^ 54) := by
  have hpow : delta ^ (-((2 : Real) ^ (21 : Nat))) = (delta⁻¹) ^ (2 ^ 21 : Nat) := by
    rw [Real.rpow_neg hδ.le, show ((2 : Real) ^ (21 : Nat)) = ((2 ^ 21 : Nat) : Real) by push_cast; ring,
      Real.rpow_natCast, inv_pow]
  unfold section13Q
  rw [hpow]
  have h1 : (2 : Real) ^ ((2 : Nat) ^ 20) ≤ X ^ (2 ^ 20) := pw_const hX le_rfl
  have h2 : (delta⁻¹) ^ (2 ^ 21 : Nat) ≤ X ^ (2 ^ (32 + 21)) :=
    pw_pow hX (inv_nonneg.mpr hδ.le) hδinv le_rfl
  exact pw_mono hX (pw_mul' hX (pow_nonneg (inv_nonneg.mpr hδ.le) _) h1 h2)
    (by norm_num)

/-- `(polyRowExponent p δ)⁻¹ ≤ X^(2^69)` once `δ⁻¹ ≤ X^(2^32)` and `p ≤ 2^(2^64)`. -/
theorem polyRowExponent_inv_le_pw (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδone : delta ≤ 1) (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) {p : Nat}
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    (polyRowExponent p delta)⁻¹ ≤ X ^ (2 ^ 69) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Real, Q = section13Q delta := ⟨_, rfl⟩
  have hQ : Q ≤ X ^ (2 ^ 54) := by rw [hQdef]; exact section13Q_le_pw hX hδ hδinv
  have hQ512 : (512 : Real) ≤ Q := by rw [hQdef]; exact section13Q_ge_512 hδ hδone
  have hQ1 : Q + 1 ≤ X * X ^ (2 ^ 54) := by
    linarith only [mul_le_mul hX hQ (by linarith only [hQ512]) (by linarith only [hX]), hQ512]
  have h4 : (4 : Real) ≤ X ^ 2 := by nlinarith only [hX]
  have hp := pw_const hX hpB
  unfold polyRowExponent
  rw [inv_inv, ← hQdef]
  calc _ ≤ X ^ 2 * (X ^ (2 ^ 54)) ^ 3 * (X * X ^ (2 ^ 64) * (X * X ^ (2 ^ 54)) ^ 8) ^ 4 := by
        gcongr
    _ = X ^ (2 + 3 * 2 ^ 54 + 4 * (1 + 2 ^ 64 + 8 * (1 + 2 ^ 54))) := by ring
    _ ≤ X ^ (2 ^ 69) := pow_le_pow_right₀ (by linarith only [hX]) (by norm_num)

theorem section13PolySquareFactorF_inv_le (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) :
    ((2 : Real) ^ (-(100 : Int)) * delta ^ 448)⁻¹ ≤ X ^ (2 ^ 42) := by
  have h1 : ((2 : Real) ^ (-(100 : Int)))⁻¹ ≤ X ^ (2 ^ 7) := by
    rw [zpow_neg, inv_inv, zpow_ofNat]
    exact pw_const hX (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h2 : (delta ^ 448)⁻¹ ≤ X ^ (2 ^ (32 + 9)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_nonneg.mpr hδ.le) hδinv (by norm_num)
  exact pw_mono hX (inv_mul_le_pw hX (by positivity) h1 h2) (by norm_num)

/-- The third square factor `g = cor711Exponent (2^(−135)δ^704) 1` lies in
`(0, 1]`, and `g⁻¹ ≤ X^(2^45)`. -/
theorem section13PolySquareFactorG_bounds (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδone : delta ≤ 1) (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) :
    0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 ∧
      cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 ≤ 1 ∧
      (cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1)⁻¹ ≤ X ^ (2 ^ 45) := by
  have hb : 0 < (2 : Real) ^ (-(135 : Int)) * delta ^ 704 := by positivity
  have hb1 : (2 : Real) ^ (-(135 : Int)) * delta ^ 704 ≤ 1 :=
    mul_le_one₀ (by norm_num) (by positivity) (pow_le_one₀ hδ.le hδone)
  have hbinv := inv_mul_le_pw hX (pow_pos hδ 704)
    (pw_const hX (by norm_num) : ((2 : Real) ^ (-(135 : Int)))⁻¹ ≤ X ^ (2 ^ 8))
    ((inv_pow delta 704).symm.trans_le
      (pw_pow hX (inv_nonneg.mpr hδ.le) hδinv (by norm_num : 704 ≤ 2 ^ 10)))
  unfold cor711Exponent
  rw [Nat.cast_one, inv_one, mul_one, sq]
  exact ⟨by positivity, mul_le_one₀ (by norm_num) (by positivity) (mul_le_one₀ hb1 hb.le hb1),
    pw_mono hX (inv_mul_le_pw hX (mul_pos hb hb)
      (pw_const hX (by norm_num) : ((2 : Real) ^ (-(14 : Real)))⁻¹ ≤ X ^ (2 ^ 4))
      (inv_mul_le_pw hX hb hbinv hbinv)) (by norm_num)⟩

/-- The polynomial square exponent is positive, at most `1/2`, and its
inverse is at most `X^(2^72)`. -/
theorem section13PolySquareExponent_bounds (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδone : delta ≤ 1) (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) {p : Nat} (hp : 0 < p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    0 < section13PolySquareExponent p delta ∧ section13PolySquareExponent p delta ≤ 1 / 2 ∧
      (section13PolySquareExponent p delta)⁻¹ ≤ X ^ (2 ^ 72) := by
  have hr := polyRowExponent_pos hδ hδone hp
  have hr2 := two_mul_polyRowExponent_le_one hδ hδone hp
  have hf : 0 < (2 : Real) ^ (-(100 : Int)) * delta ^ 448 := by positivity
  have hf1 : (2 : Real) ^ (-(100 : Int)) * delta ^ 448 ≤ 1 :=
    mul_le_one₀ (by norm_num) (by positivity) (pow_le_one₀ hδ.le hδone)
  obtain ⟨hg, hg1, hginv⟩ := section13PolySquareFactorG_bounds hX hδ hδone hδinv
  have hrfg := inv_mul_le_pw hX hg (inv_mul_le_pw hX hf
    (polyRowExponent_inv_le_pw hX hδ hδone hδinv hpB)
    (section13PolySquareFactorF_inv_le hX hδ hδinv)) hginv
  unfold section13PolySquareExponent
  refine ⟨div_pos (mul_pos (mul_pos hr hf) hg) (by norm_num), ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right (mul_le_one₀ (mul_le_one₀ (by linarith only [hr2]) hf.le hf1)
      hg.le hg1) (by norm_num)).trans (by norm_num)
  · rw [inv_div, div_eq_mul_inv]
    exact pw_mono hX (pw_mul' hX (inv_pos.mpr (mul_pos (mul_pos hr hf) hg)).le
      (pw_const hX (by norm_num) : (4 : Real) ≤ X ^ (2 ^ 1)) hrfg) (by norm_num)

end Envelope

/-- The degree-three discrepancy exponent at the polynomial square exponent:
`σ⁻¹ ≤ (2/α)^(2^74)`. -/
theorem fejerCubicDiscrepancyExponentAt_poly_bounds {alpha : Real} (hα : 0 < alpha)
    (hα2 : alpha ≤ 1 / 2) {p : Nat} (hp : 0 < p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    0 < fejerCubicDiscrepancyExponentAt alpha
        (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat))) ∧
      (fejerCubicDiscrepancyExponentAt alpha
        (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat))))⁻¹ ≤
        (2 / alpha) ^ (2 ^ 74) := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  have hX : 2 ≤ 2 / alpha := two_div_ge_two hα hα2
  obtain ⟨he, -, heinv⟩ := section13PolySquareExponent_bounds
    (delta := (alpha / 2) ^ (4207554485 : Nat)) hX (by positivity)
    (pow_le_one₀ (by positivity) (by linarith only [hαone]))
    (by rw [← inv_pow, inv_div]; exact pw_natpow hX (by norm_num)) hp hpB
  have hκ := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hek := inv_mul_le_pw hX hκ heinv (fejerCubicLocalCountExponent_inv_le_power hα hαone)
  have hK : 2 * (polynomialPartitionConstant 3 : Real) ≤ (2 / alpha) ^ (2 ^ 7) :=
    pw_const hX (by norm_num [polynomialPartitionConstant, Nat.factorial])
  unfold fejerCubicDiscrepancyExponentAt phaseInverseExponent
  refine ⟨div_pos (mul_pos he hκ) (by unfold polynomialPartitionConstant; positivity), ?_⟩
  rw [inv_div, div_eq_mul_inv]
  exact pw_mono hX (pw_mul' hX (inv_pos.mpr (mul_pos he hκ)).le hK hek) (by norm_num)

/-- A degree-`d` discrepancy bound with polynomial envelopes for `β` and `σ`. -/
def PolyEnvBound (d μ : Nat) : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ beta sigma T : Real, FunctionDiscrepancyBound d alpha beta sigma T ∧
      0 < beta ∧ beta ≤ 1 ∧ 0 < sigma ∧ sigma ≤ 16 ∧
      beta⁻¹ ≤ (2 / alpha) ^ (2 ^ μ) ∧ sigma⁻¹ ≤ (2 / alpha) ^ (2 ^ μ)

theorem PolyEnvBound.mono {d μ μ' : Nat} (h : PolyEnvBound d μ) (hμ : μ ≤ μ') :
    PolyEnvBound d μ' := by
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, b1, s0, s16, bi, si⟩ := h alpha ha ha2
  have hX := two_div_ge_two ha ha2
  exact ⟨b, s, T, hB, b0, b1, s0, s16, pw_mono hX bi hμ, pw_mono hX si hμ⟩

/-! ### The threshold of the polynomial chain -/

theorem positivePowerThreshold_anti {C D e e' : Real} (he : 0 < e) (hee : e ≤ e') :
    positivePowerThreshold C D e' ≤ positivePowerThreshold C D e := by
  unfold positivePowerThreshold
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (inv_anti₀ he hee))

theorem uniformRoundedPowerThreshold_anti {c d z e e' : Real} (he : 0 < e) (hee : e ≤ e') :
    uniformRoundedPowerThreshold c d z e' ≤ uniformRoundedPowerThreshold c d z e := by
  unfold uniformRoundedPowerThreshold
  exact max_le_max (positivePowerThreshold_anti he hee)
    (max_le_max (positivePowerThreshold_anti he hee) (positivePowerThreshold_anti he hee))

theorem squarePowerThreshold_anti {c e e' f g : Real} (he : 0 < e) (hee : e ≤ e')
    (hf : 0 < f) (hg : 0 < g) : squarePowerThreshold c e' f g ≤ squarePowerThreshold c e f g := by
  have h1 := mul_le_mul_of_nonneg_right hee hf.le
  have h2 := mul_le_mul_of_nonneg_right h1 hg.le
  unfold squarePowerThreshold
  exact max_le_max (positivePowerThreshold_anti (mul_pos he hf) h1)
    (positivePowerThreshold_anti (by positivity) (by linarith only [h2]))

/-- The polynomial geometric threshold is at most the explicit one. -/
theorem section13PolyGeometricThreshold_le {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1)
    {p : Nat} (hp : 0 < p) (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    section13PolyGeometricThreshold p delta ≤ section13GeometricThreshold delta := by
  have hre := catalogue_length_exponent_le_polyRowExponent hδ hδone hp hpB
  have he : (0 : Real) < 1 / (2 : Real) ^ (13 * section13Q delta) := by positivity
  have hf : 0 < (2 : Real) ^ (-(100 : Int)) * delta ^ 448 := by positivity
  have hg : 0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 := by
    unfold cor711Exponent; positivity
  have hint : section13PolyIntegerThreshold p delta ≤ section13DensityIntegerThreshold delta := by
    unfold section13PolyIntegerThreshold section13DensityIntegerThreshold
    exact Finset.sup_mono_fun fun q _ => Nat.ceil_mono <| by
      unfold section13PolyBudgetThreshold section13IntegerBudgetThreshold
      exact max_le_max (uniformRoundedPowerThreshold_anti he hre) le_rfl
  unfold section13PolyGeometricThreshold section13GeometricThreshold squareScaleThreshold
  exact max_le_max le_rfl (le_max_of_le_right (max_le_max (Nat.cast_le.mpr hint)
    (max_le_max (positivePowerThreshold_anti he hre) (squarePowerThreshold_anti he hre hf hg))))

/-- The polynomial square exponent is at least the explicit one. -/
theorem section13SquareExponent_le_poly {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1)
    {p : Nat} (hp : 0 < p) (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    section13SquareExponent delta ≤ section13PolySquareExponent p delta := by
  have hf : 0 < (2 : Real) ^ (-(100 : Int)) * delta ^ 448 := by positivity
  have hg : 0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 := by
    unfold cor711Exponent; positivity
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (catalogue_length_exponent_le_polyRowExponent hδ hδone hp hpB) hf.le) hg.le
  unfold section13SquareExponent section13PolySquareExponent
  linarith only [h]

/-- **The threshold of the polynomial chain** is at most the explicit
`fejerCubicInverseThreshold α`: the same positive-power thresholds at larger
exponents, above a smaller geometric threshold. -/
theorem fejerCubicInverseThresholdAt_poly_le {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {p : Nat} (hp : 0 < p) (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    fejerCubicInverseThresholdAt alpha
        (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat)))
        (max (max (section13FrequencyGraphThreshold alpha : Real)
            (section13PolyGeometricThreshold p ((alpha / 2) ^ (4207554485 : Nat))))
          (positivePowerThreshold 4 1
            (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat))))) ≤
      fejerCubicInverseThreshold alpha := by
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := by positivity
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 := pow_le_one₀ (by positivity)
    (by linarith only [hαone])
  have hl0 : 0 < fejerCubicLocalizationExponent alpha := Real.rpow_pos_of_pos (by norm_num) _
  have hl := (section13_fejer_exponent_lower hα hαone).trans
    (section13SquareExponent_le_poly hδ hδone hp hpB)
  have hκ := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hK : (0 : Real) < 2 * (polynomialPartitionConstant 3 : Real) := by
    unfold polynomialPartitionConstant; positivity
  exact max_le_max (max_le_max le_rfl (max_le_max (max_le_max (max_le_max le_rfl
    (section13PolyGeometricThreshold_le hδ hδone hp hpB)) (positivePowerThreshold_anti hl0 hl))
    (positivePowerThreshold_anti hl0 hl)))
    (positivePowerThreshold_anti (div_pos (mul_pos hl0 hκ) hK)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hκ.le) hK.le))

/-- **Degree three from the polynomial chain**, from a phase partition:
polynomial `β` and `σ`, and a doubly exponential threshold. -/
theorem polyCubic_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) {alpha : Real} (hα : 0 < alpha)
    (hα2 : alpha ≤ 1 / 2) :
    ∃ beta sigma T : Real, FunctionDiscrepancyBound 3 alpha beta sigma T ∧
      0 < beta ∧ beta ≤ 1 ∧ 0 < sigma ∧ sigma ≤ 16 ∧
      beta⁻¹ ≤ (2 / alpha) ^ (2 ^ 59) ∧ sigma⁻¹ ≤ (2 / alpha) ^ (2 ^ 74) ∧
      T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ 62))) := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  have hX : 2 ≤ 2 / alpha := two_div_ge_two hα hα2
  obtain ⟨he, hehalf, -⟩ := section13PolySquareExponent_bounds
    (delta := (alpha / 2) ^ (4207554485 : Nat)) hX (by positivity)
    (pow_le_one₀ (by positivity) (by linarith only [hαone]))
    (by rw [← inv_pow, inv_div]; exact pw_natpow hX (by norm_num)) hp hpB
  obtain ⟨hσ, hσinv⟩ := fejerCubicDiscrepancyExponentAt_poly_bounds hα hα2 hp hpB
  refine ⟨fejerCubicDiscrepancyParameter alpha, _, _,
    (fejerSquareAt_poly hα hαone hpp hp hK hpB).functionDiscrepancyBound hα hαone he hehalf,
    fejerCubicDiscrepancyParameter_pos hα, fejerCubicDiscrepancyParameter_le_one hα hαone,
    hσ, ?_, fejerCubicDiscrepancyParameter_inv_le_power hα hαone, hσinv,
    (fejerCubicInverseThresholdAt_poly_le hα hαone hp hpB).trans
      (fejerCubicInverseThreshold_le_double_exp hα hαone)⟩
  obtain ⟨hκ, hκ1⟩ := fejerCubicLocalCountExponent_bounds hα hαone
  have hK3 : (1 : Real) ≤ polynomialPartitionConstant 3 := by exact_mod_cast polyPartConst_pos 3
  exact (div_le_self (mul_pos he hκ).le (by linarith only [hK3])).trans
    (by nlinarith only [hehalf, hκ, hκ1])

/-- **Degree three with polynomial envelopes**, from a phase partition. -/
theorem polyEnvBound_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : PolyEnvBound 3 74 := by
  intro alpha hα hα2
  obtain ⟨b, s, T, hB, b0, b1, s0, s16, bi, si, -⟩ :=
    polyCubic_three_of_phase_partition hpp hp hK hpB hα hα2
  exact ⟨b, s, T, hB, b0, b1, s0, s16, pw_mono (two_div_ge_two hα hα2) bi (by norm_num), si⟩

/-- **Degree three for the Theorem 18.2 envelope**, from a phase partition:
the polynomial chain fits `EnvBound 3 62`, the constant of the explicit base
`envBound_three`. -/
theorem envBound_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : EnvBound 3 62 := by
  intro alpha hα hα2
  have hX := two_div_ge_two hα hα2
  obtain ⟨b, s, T, hB, b0, b1, s0, s16, bi, si, hT⟩ :=
    polyCubic_three_of_phase_partition hpp hp hK hpB hα hα2
  refine ⟨b, s, T, hB, b0, b1, s0, s16, pw_mono hX bi (by norm_num), ?_, hT⟩
  exact si.trans ((pow_two_pow_le_exp_pow_succ hX 74).trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith only [hX]) (by norm_num))))

end LeanProofs.GowersSzemeredi
