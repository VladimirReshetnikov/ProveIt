import GowersSzemeredi.Proofs13PolySquareExtraction
import GowersSzemeredi.Proofs18FejerCubicAt
import GowersSzemeredi.Proofs18FejerReciprocalBudgets
import GowersSzemeredi.Proofs18EnvelopeBounds
import GowersSzemeredi.Proofs18TheoremOneDegrees

/-! **Theorem 18.1 at degree three**, from a polynomial phase partition
(Notes L.7c, P10a).

`Theorem181At 3` asks for a discrepancy partition with parameter and
average-cell exponent at least `section18Exponent α 3 = α^(2^8192)`.
* The corpus parameter `fejerCubicDiscrepancyParameter α` is polynomial,
  `β⁻¹ ≤ (2/α)^(2^59)`.
* The corpus exponent is doubly exponential: its square exponent carries the
  catalogue row exponent `2^(−13Q)`.

The module also supplies `PolyEnvBound`, its monotonicity and conversion
to Theorem 18.1, and `polyEnvBound_three_of_phase_partition`. The printed
degree-three theorem specializes this shared polynomial base.

Here the square comes from `section13_complete_square_extraction_poly`, at
the density `δ = (α/2)^4207554485` of the corpus frequency graph
(`fejerSquareAt_poly`). The resulting σ satisfies `σ⁻¹ ≤ (2/α)^(2^74)`:
* the row exponent contributes `2^69`;
* the two square factors contribute `2^42` and `2^45`;
* the local count exponent contributes `2^59`.

`theorem_18_1_three_of_phase_partition` takes the phase partition as a
hypothesis. Its constants need `K ≤ 2^p` and `p ≤ 2^(2^64)`; since
`ProgressionPhasePartition.mono` raises `p` freely, the explicit constants of
`CommonDiffPartitionBoundAt 1` qualify (bridge). -/
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
  have hδ : 0 < delta := pow_pos (by positivity) _
  have hδone : delta ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hαone])
  intro N _ _ hN f hf hnot
  have hNgraph : section13FrequencyGraphThreshold alpha ≤ N := by
    exact_mod_cast ((le_max_left _ _).trans hN :
      (section13FrequencyGraphThreshold alpha : Real) ≤ N)
  obtain ⟨A, psi, hA, hfreiman, hmostly, hfourier⟩ :=
    section13_fejer_frequency_graph_explicit alpha hα hαone N hNgraph f hf hnot
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hNpos _
  let beta := (A.card : Real) / (N : Real) ^ 2
  have hδβ : delta ≤ beta := (le_div_iff₀ hN2).mpr hA
  have hcard : (A.card : Real) ≤ (N : Real) ^ 2 := by
    have hc : A.card ≤ N * N := by
      simpa only [Pair, Fintype.card_prod, ZMod.card] using Finset.card_le_univ A
    exact_mod_cast (by simpa only [pow_two] using hc : A.card ≤ N ^ 2)
  have hβone : beta ≤ 1 := (div_le_one hN2).mpr hcard
  let S : Section13Context N := {
    A := A
    phi := psi
    alpha := beta
    eta := (2 : Real) ^ (-(44 : Int))
    alpha_pos := hδ.trans_le hδβ
    alpha_at_most_one := hβone
    card_A := (div_mul_cancel₀ (A.card : Real) hN2.ne').symm
    separately_freiman := hfreiman
    eta_value := rfl
    mostly_respected := hmostly }
  obtain ⟨P, Q, B, hPs, hPQ, hP, hQ, hlen, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_complete_square_extraction_poly hδ hδone hpp hp hK hpB N S hδβ
      ((le_max_right _ _).trans hN)
  obtain ⟨mu, hmu, hagree⟩ := hbil
  refine ⟨P, Q, B, mu, hPs, hPQ, hP, hQ, hlen, hsize, hbox, ?_,
    ⟨mu, hmu, fun _ _ => rfl⟩, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (section13_fejer_square_density hα hαone) (Nat.cast_nonneg P.length))
      (Nat.cast_nonneg Q.length)).trans hmass
  · intro z hz
    have heq : psi z = mu z := hagree z hz
    rw [← heq]
    exact hfourier z (hBA hz)

/-! ### The envelope of the polynomial exponent -/

section Envelope

variable {X : Real}

theorem inv_mul_le_pw (hX : 2 ≤ X) {x y : Real} (hx : 0 < x) (hy : 0 < y) {a b : Nat}
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
  have hQ0 : 0 ≤ Q := by linarith only [hQ512]
  have hQ10 : 0 ≤ Q + 1 := by linarith only [hQ512]
  have h2 : (2 : Real) ≤ X ^ (2 ^ 0) := pw_const hX (by norm_num)
  have hQ1 : Q + 1 ≤ X ^ (2 ^ 55) := by
    have h := pw_mul' hX hQ0 h2 hQ
    exact (by linarith only [hQ512] : Q + 1 ≤ 2 * Q).trans (pw_mono hX h (by norm_num))
  have hQ8 : (Q + 1) ^ 8 ≤ X ^ (2 ^ (55 + 3)) := pw_pow hX hQ10 hQ1 (by norm_num)
  have hp : (p : Real) ≤ X ^ (2 ^ 64) := pw_const hX hpB
  have h2p0 : 0 ≤ 2 * (p : Real) := mul_nonneg (by norm_num) (Nat.cast_nonneg p)
  have h2p : 2 * (p : Real) ≤ X ^ (2 ^ 65) :=
    pw_mono hX (pw_mul' hX (Nat.cast_nonneg p) h2 hp) (by norm_num)
  have hc0 : 0 ≤ 2 * (p : Real) * (Q + 1) ^ 8 := mul_nonneg h2p0 (pow_nonneg hQ10 8)
  have hc : 2 * (p : Real) * (Q + 1) ^ 8 ≤ X ^ (2 ^ 66) :=
    pw_mono hX (pw_mul' hX (pow_nonneg hQ10 8) h2p hQ8) (by norm_num)
  have hc4 : (2 * (p : Real) * (Q + 1) ^ 8) ^ 4 ≤ X ^ (2 ^ (66 + 2)) :=
    pw_pow hX hc0 hc (by norm_num)
  have hQ3 : Q ^ 3 ≤ X ^ (2 ^ (54 + 2)) := pw_pow hX hQ0 hQ (by norm_num)
  have h4 : (4 : Real) ≤ X ^ (2 ^ 1) := pw_const hX (by norm_num)
  have h4Q0 : 0 ≤ 4 * Q ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hQ0 3)
  have h4Q : 4 * Q ^ 3 ≤ X ^ (2 ^ 57) :=
    pw_mono hX (pw_mul' hX (pow_nonneg hQ0 3) h4 hQ3) (by norm_num)
  unfold polyRowExponent
  rw [inv_inv, ← hQdef]
  exact pw_mono hX (pw_mul' hX (pow_nonneg hc0 4) h4Q hc4) (by norm_num)

theorem section13PolySquareFactorF_inv_le (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) :
    ((2 : Real) ^ (-(100 : Int)) * delta ^ 448)⁻¹ ≤ X ^ (2 ^ 42) := by
  have h1 : ((2 : Real) ^ (-(100 : Int)))⁻¹ ≤ X ^ (2 ^ 7) := by
    rw [zpow_neg, inv_inv, zpow_ofNat]
    exact pw_const hX (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h2 : (delta ^ 448)⁻¹ ≤ X ^ (2 ^ (32 + 9)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_nonneg.mpr hδ.le) hδinv (by norm_num)
  exact pw_mono hX (inv_mul_le_pw hX (by positivity) (by positivity) h1 h2) (by norm_num)

/-- The third square factor `g = cor711Exponent (2^(−135)δ^704) 1` lies in
`(0, 1]`, and `g⁻¹ ≤ X^(2^45)`. -/
theorem section13PolySquareFactorG_bounds (hX : 2 ≤ X) {delta : Real} (hδ : 0 < delta)
    (hδone : delta ≤ 1) (hδinv : delta⁻¹ ≤ X ^ (2 ^ 32)) :
    0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 ∧
      cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 ≤ 1 ∧
      (cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1)⁻¹ ≤ X ^ (2 ^ 45) := by
  have ha1 : 0 < (2 : Real) ^ (-(14 : Real)) := Real.rpow_pos_of_pos (by norm_num) _
  have ha1le : (2 : Real) ^ (-(14 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have ha1inv : ((2 : Real) ^ (-(14 : Real)))⁻¹ ≤ X ^ (2 ^ 4) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (14 : Real) = ((14 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pw_const hX (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have ha2 : 0 < (2 : Real) ^ (-(135 : Int)) := by positivity
  have ha2le : (2 : Real) ^ (-(135 : Int)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have ha2inv : ((2 : Real) ^ (-(135 : Int)))⁻¹ ≤ X ^ (2 ^ 8) := by
    rw [zpow_neg, inv_inv, zpow_ofNat]
    exact pw_const hX (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have ha3 : 0 < delta ^ 704 := pow_pos hδ _
  have ha3inv : (delta ^ 704)⁻¹ ≤ X ^ (2 ^ (32 + 10)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_nonneg.mpr hδ.le) hδinv (by norm_num)
  have hb : 0 < (2 : Real) ^ (-(135 : Int)) * delta ^ 704 := mul_pos ha2 ha3
  have hble : (2 : Real) ^ (-(135 : Int)) * delta ^ 704 ≤ 1 :=
    mul_le_one₀ ha2le ha3.le (pow_le_one₀ hδ.le hδone)
  have hbinv := inv_mul_le_pw hX ha2 ha3 ha2inv ha3inv
  have hb2inv : (((2 : Real) ^ (-(135 : Int)) * delta ^ 704) ^ 2)⁻¹ ≤ X ^ (2 ^ (max 8 (32 + 10) + 1 + 1)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_nonneg.mpr hb.le) hbinv (by norm_num)
  have hall := inv_mul_le_pw hX ha1 (pow_pos hb 2) ha1inv hb2inv
  unfold cor711Exponent
  rw [Nat.cast_one, inv_one, mul_one]
  refine ⟨mul_pos ha1 (pow_pos hb 2), mul_le_one₀ ha1le (pow_pos hb 2).le (pow_le_one₀ hb.le hble),
    pw_mono hX hall (by norm_num)⟩

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
    mul_le_one₀ (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)) (by positivity)
      (pow_le_one₀ hδ.le hδone)
  obtain ⟨hg, hg1, hginv⟩ := section13PolySquareFactorG_bounds hX hδ hδone hδinv
  have h4 : ((4 : Real)⁻¹)⁻¹ ≤ X ^ (2 ^ 1) := by rw [inv_inv]; exact pw_const hX (by norm_num)
  have hrf := inv_mul_le_pw hX hr hf (polyRowExponent_inv_le_pw hX hδ hδone hδinv hpB)
    (section13PolySquareFactorF_inv_le hX hδ hδinv)
  have hrfg := inv_mul_le_pw hX (mul_pos hr hf) hg hrf hginv
  have hall := inv_mul_le_pw hX (mul_pos (mul_pos hr hf) hg) (by norm_num : (0 : Real) < 4⁻¹) hrfg h4
  unfold section13PolySquareExponent
  refine ⟨div_pos (mul_pos (mul_pos hr hf) hg) (by norm_num), ?_, ?_⟩
  · have hprod : polyRowExponent p delta * ((2 : Real) ^ (-(100 : Int)) * delta ^ 448) *
        cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 ≤ 1 / 2 * 1 * 1 :=
      mul_le_mul (mul_le_mul (by linarith only [hr2]) hf1 hf.le (by norm_num)) hg1 hg.le
        (by norm_num)
    linarith only [hprod]
  · rw [div_eq_mul_inv]
    exact pw_mono hX hall (by norm_num)

end Envelope

/-- `section18Exponent α k ≤ x` once `x⁻¹ ≤ (2/α)^(2^μ)` with `μ + 1 ≤ 2^(k+10)`. -/
theorem section18Exponent_le_of_inv_le {alpha : Real} (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2)
    {x : Real} (hx : 0 < x) {μ k : Nat} (hμ : μ + 1 ≤ 2 ^ (k + 10))
    (hxinv : x⁻¹ ≤ (2 / alpha) ^ (2 ^ μ)) : section18Exponent alpha k ≤ x := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  unfold section18Exponent
  have h1 : alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 10))) ≤ alpha ^ (2 ^ (μ + 1)) :=
    pow_le_pow_of_le_one hα.le hαone (Nat.pow_le_pow_right (by norm_num) hμ)
  have h2 : alpha ^ (2 ^ (μ + 1)) = (alpha ^ 2) ^ (2 ^ μ) := by
    rw [pow_succ, mul_comm (2 ^ μ) 2, pow_mul]
  have h3 : (alpha ^ 2) ^ (2 ^ μ) ≤ (alpha / 2) ^ (2 ^ μ) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [hα, hα2]) _
  have h4 : (alpha / 2) ^ (2 ^ μ) = ((2 / alpha) ^ (2 ^ μ))⁻¹ := by rw [← inv_pow, inv_div]
  have h5 : ((2 / alpha) ^ (2 ^ μ))⁻¹ ≤ x := by
    have h := inv_anti₀ (inv_pos.mpr hx) hxinv
    rwa [inv_inv] at h
  calc _ ≤ alpha ^ (2 ^ (μ + 1)) := h1
    _ = (alpha ^ 2) ^ (2 ^ μ) := h2
    _ ≤ (alpha / 2) ^ (2 ^ μ) := h3
    _ = ((2 / alpha) ^ (2 ^ μ))⁻¹ := h4
    _ ≤ x := h5

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
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hαone])
  have hδinv : ((alpha / 2) ^ (4207554485 : Nat))⁻¹ ≤ (2 / alpha) ^ (2 ^ 32) := by
    rw [← inv_pow, inv_div]
    exact pw_natpow hX (by norm_num)
  obtain ⟨he, _, heinv⟩ := section13PolySquareExponent_bounds hX hδ hδone hδinv hp hpB
  have hκ := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hκinv := fejerCubicLocalCountExponent_inv_le_power hα hαone
  have hK3 : (0 : Real) < 2 * (polynomialPartitionConstant 3 : Real) := by
    unfold polynomialPartitionConstant; positivity
  have hK3le : ((2 * (polynomialPartitionConstant 3 : Real))⁻¹)⁻¹ ≤ (2 / alpha) ^ (2 ^ 7) := by
    rw [inv_inv]
    apply pw_const hX
    unfold polynomialPartitionConstant
    norm_num [Nat.factorial]
  have hek := inv_mul_le_pw hX he hκ heinv hκinv
  have hall := inv_mul_le_pw hX (mul_pos he hκ) (inv_pos.mpr hK3) hek hK3le
  unfold fejerCubicDiscrepancyExponentAt phaseInverseExponent
  refine ⟨div_pos (mul_pos he hκ) hK3, ?_⟩
  rw [div_eq_mul_inv]
  exact pw_mono hX hall (by norm_num)

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

/-- **Theorem 18.1 from a polynomial envelope** that fits `2^(d+10)`. -/
theorem theorem181At_of_polyEnvBound {d μ : Nat} (h : PolyEnvBound d μ)
    (hμ : μ + 1 ≤ 2 ^ (d + 10)) : Theorem181At d := by
  apply Theorem181At.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, -, s0, -, bi, si⟩ := h alpha ha ha2
  exact ⟨b, s, T, section18Exponent_le_of_inv_le ha ha2 b0 hμ bi,
    section18Exponent_le_of_inv_le ha ha2 s0 hμ si, hB⟩

/-- **Degree three with polynomial envelopes**, from a phase partition. -/
theorem polyEnvBound_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : PolyEnvBound 3 74 := by
  intro alpha hα hα2
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  have hX : 2 ≤ 2 / alpha := two_div_ge_two hα hα2
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hαone])
  have hδinv : ((alpha / 2) ^ (4207554485 : Nat))⁻¹ ≤ (2 / alpha) ^ (2 ^ 32) := by
    rw [← inv_pow, inv_div]
    exact pw_natpow hX (by norm_num)
  obtain ⟨he, hehalf, _⟩ := section13PolySquareExponent_bounds hX hδ hδone hδinv hp hpB
  obtain ⟨hσ, hσinv⟩ := fejerCubicDiscrepancyExponentAt_poly_bounds hα hα2 hp hpB
  obtain ⟨hκ, hκ1⟩ := fejerCubicLocalCountExponent_bounds hα hαone
  have hK3 : (1 : Real) ≤ (polynomialPartitionConstant 3 : Real) := by
    exact_mod_cast polyPartConst_pos 3
  have hσ16 : fejerCubicDiscrepancyExponentAt alpha
      (section13PolySquareExponent p ((alpha / 2) ^ (4207554485 : Nat))) ≤ 16 := by
    unfold fejerCubicDiscrepancyExponentAt phaseInverseExponent
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [he, hehalf, hκ, hκ1, hK3]
  refine ⟨fejerCubicDiscrepancyParameter alpha, _, _,
    (fejerSquareAt_poly hα hαone hpp hp hK hpB).functionDiscrepancyBound hα hαone he hehalf,
    fejerCubicDiscrepancyParameter_pos hα, fejerCubicDiscrepancyParameter_le_one hα hαone,
    hσ, hσ16, ?_, hσinv⟩
  exact pw_mono hX (fejerCubicDiscrepancyParameter_inv_le_power hα hαone) (by norm_num)

/-- **Theorem 18.1 at degree three**, from a polynomial phase partition of
progressions with `K ≤ 2^p` and `p ≤ 2^(2^64)`. -/
theorem theorem_18_1_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : Theorem181At 3 := by
  exact theorem181At_of_polyEnvBound
    (polyEnvBound_three_of_phase_partition hpp hp hK hpB) (by norm_num)

end LeanProofs.GowersSzemeredi
