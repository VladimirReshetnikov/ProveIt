import GowersSzemeredi.Proofs16GlobalColumnAgreement

/-! The zero-core agreement density is triple-exponentially small.

`global_column_shifted_agreement` guarantees an agreement set of density
`globalColumnAgreementDensity alpha`. This module bounds that density from
above, from the definitions alone. Write `d = columnSpectrumCap (columnEightDensity alpha)`.
* `globalColumnWordDensity_le_witness`: the word density is at most the
  witness density, hence at most `13^(-d)`.
* `thirteen_pow_le_globalColumnModelRank`: so the model rank
  `g = ⌈4d/δ⌉` is at least `13^d`.
* `modelTestDensity_le_inv_two_pow`: the test density is at most `2^(-g)`,
  because every refinement cell count is at least two.
* `globalColumnZeroDensity_le`: elimination takes at least `log 2/β`
  rounds, each costing `β/10 ≤ e⁻¹`, so the zero-core density is at most
  `exp(-2^g/2)`.
* `globalColumnAgreementDensity_le_triple_exp`: the guaranteed agreement
  density is at most `exp(-2^(13^d)/2)`.
* `globalColumnAgreementDensity_lt_polynomial_contract`: for `alpha ≤ 1/2`
  and `K ≤ 2^64` it is below `exp(-(4/alpha)^K)`. That is the agreement
  `DeepStructureAt Bnd` demands at density `alpha` when `Bnd alpha ≤ (4/alpha)^K`,
  the hypothesis of `theorem_16_2_at_three_of_eventually`.

The steps are stated generically, so that `Proofs16CoherentAnchorGrowth`
reuses them for the even core and the coherent anchors:
`thirteen_pow_le_rank_ceil` (any rank `⌈m·d/δ_k⌉`, `m ≥ 1`),
`elimination_density_le` (any per-round divisor `m ≥ 1`) and
`lt_polynomial_contract_of_le_triple_exp`.

These are upper bounds on the density the current parameters guarantee,
not on the actual agreement set. They show that the zero-core chain, as
parametrized, cannot supply the polynomial contract; they do not show
that no route can. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem succ_le_two_pow (d : Nat) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem columnEightDensity_le_half {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    columnEightDensity alpha ≤ alpha / 2 := by
  unfold columnEightDensity
  have h1 : (2 : Real) ^ (-(1882 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h2 : ((alpha / 2) ^ 4) ^ 1164 ≤ alpha / 2 := by
    rw [← pow_mul]
    exact pow_le_of_le_one (by positivity) (by linarith) (by norm_num)
  have h0 : (0 : Real) ≤ ((alpha / 2) ^ 4) ^ 1164 := by positivity
  calc (2 : Real) ^ (-(1882 : Real)) * ((alpha / 2) ^ 4) ^ 1164
      ≤ 1 * (alpha / 2) := mul_le_mul h1 h2 h0 zero_le_one
    _ = alpha / 2 := one_mul _

theorem columnEightDensity_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    columnEightDensity alpha ≤ 1 :=
  (columnEightDensity_le_half ha ha1).trans (by linarith)

/-- The witness density pays `13` per spectral frequency. -/
theorem columnWitnessDensity_le {beta : Real} (hb : 0 < beta) (hb1 : beta ≤ 1) :
    columnWitnessDensity beta ≤ 1 / (13 : Real) ^ columnSpectrumCap beta := by
  unfold columnWitnessDensity
  have h4 : beta ^ 4 ≤ 1 := pow_le_one₀ hb.le hb1
  obtain ⟨X, hX⟩ : ∃ X : Real, (13 : Real) ^ columnSpectrumCap beta = X := ⟨_, rfl⟩
  have hp : 0 < X := by rw [← hX]; positivity
  rw [hX, div_le_div_iff₀ (by positivity) hp]
  have := mul_le_mul_of_nonneg_right h4 hp.le
  linarith

theorem columnWitnessDensity_le_one {beta : Real} (hb : 0 < beta) (hb1 : beta ≤ 1) :
    columnWitnessDensity beta ≤ 1 :=
  (columnWitnessDensity_le hb hb1).trans
    (div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity))

/-- A word density never exceeds its anchor density. -/
theorem columnWordDensity_le {lambda eta : Real} (hl : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (k : Nat) :
    0 ≤ columnWordDensity lambda eta k ∧ columnWordDensity lambda eta k ≤ lambda := by
  induction k with
  | zero => exact ⟨hl, le_rfl⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hp1 : columnWordDensity lambda eta k ≤ 1 := h1.trans hl1
    show 0 ≤ eta ^ 2 * lambda ^ 3 * (columnWordDensity lambda eta k) ^ 3 / 64 ∧
      eta ^ 2 * lambda ^ 3 * (columnWordDensity lambda eta k) ^ 3 / 64 ≤ lambda
    obtain ⟨p, hp⟩ : ∃ p, columnWordDensity lambda eta k = p := ⟨_, rfl⟩
    rw [hp] at h0 h1 hp1 ⊢
    refine ⟨by positivity, ?_⟩
    have a : eta ^ 2 ≤ 1 := pow_le_one₀ he he1
    have b : lambda ^ 3 ≤ 1 := pow_le_one₀ hl hl1
    have c : p ^ 3 ≤ p := pow_le_of_le_one h0 hp1 (by norm_num)
    have hab : eta ^ 2 * lambda ^ 3 ≤ 1 := mul_le_one₀ a (by positivity) b
    have : eta ^ 2 * lambda ^ 3 * p ^ 3 ≤ 1 * p :=
      mul_le_mul hab c (by positivity) zero_le_one
    linarith

theorem globalColumnQuadrupleDensity_le_witness {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnQuadrupleDensity alpha ≤ columnWitnessDensity (columnEightDensity alpha) := by
  have hb := columnEightDensity_pos ha
  have hw0 := columnWitnessDensity_pos hb
  have hw1 := columnWitnessDensity_le_one hb (columnEightDensity_le_one ha ha1)
  have hr0 : 0 < alpha / (2 - alpha) := div_pos ha (by linarith)
  have hr1 : alpha / (2 - alpha) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  unfold globalColumnQuadrupleDensity
  obtain ⟨w, hw⟩ : ∃ w, columnWitnessDensity (columnEightDensity alpha) = w := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, alpha / (2 - alpha) = r := ⟨_, rfl⟩
  rw [hw] at hw0 hw1 ⊢
  rw [hr] at hr0 hr1 ⊢
  have h1 : w ^ 4 ≤ w := pow_le_of_le_one hw0.le hw1 (by norm_num)
  have h2 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1
  have h3 := mul_le_mul_of_nonneg_left h2 (pow_pos hw0 4).le
  linarith [pow_pos hw0 4, pow_pos hr0 4]

theorem globalColumnQuadrupleDensity_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnQuadrupleDensity alpha ≤ 1 :=
  (globalColumnQuadrupleDensity_le_witness ha ha1).trans
    (columnWitnessDensity_le_one (columnEightDensity_pos ha) (columnEightDensity_le_one ha ha1))

theorem globalColumnVertexDensity_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnVertexDensity alpha ≤ 1 := by
  have hq := globalColumnQuadrupleDensity_le_one ha ha1
  have hq0 := globalColumnQuadrupleDensity_pos ha ha1
  unfold globalColumnVertexDensity; linarith

theorem globalColumnWalkDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnWalkDensity alpha := by
  have hq0 := globalColumnQuadrupleDensity_pos ha ha1
  unfold globalColumnWalkDensity; positivity

theorem globalColumnWordDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    0 < globalColumnWordDensity alpha k := by
  have hv0 := globalColumnVertexDensity_pos ha ha1
  have hwalk0 := globalColumnWalkDensity_pos ha ha1
  have hanc0 : 0 < globalColumnAnchorDensity alpha := by
    unfold globalColumnAnchorDensity; positivity
  exact columnWordDensity_pos hanc0 hwalk0 k

/-- Every density in the word chain is at most the witness density. -/
theorem globalColumnWordDensity_le_witness {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    globalColumnWordDensity alpha k ≤ columnWitnessDensity (columnEightDensity alpha) := by
  have hq := globalColumnQuadrupleDensity_le_witness ha ha1
  have hq0 := globalColumnQuadrupleDensity_pos ha ha1
  have hq1 := globalColumnQuadrupleDensity_le_one ha ha1
  obtain ⟨q, hqq⟩ : ∃ q, globalColumnQuadrupleDensity alpha = q := ⟨_, rfl⟩
  have hwalk0 : 0 ≤ globalColumnWalkDensity alpha := (globalColumnWalkDensity_pos ha ha1).le
  have hwalk : globalColumnWalkDensity alpha ≤ globalColumnQuadrupleDensity alpha := by
    unfold globalColumnWalkDensity
    rw [hqq] at hq0 hq1 ⊢
    have : (q / 4) ^ 5 ≤ q / 4 := pow_le_of_le_one (by positivity) (by linarith) (by norm_num)
    linarith
  have hvert0 : 0 ≤ globalColumnVertexDensity alpha := (globalColumnVertexDensity_pos ha ha1).le
  have hwalk1 : globalColumnWalkDensity alpha ≤ 1 := hwalk.trans hq1
  have hvert1 := globalColumnVertexDensity_le_one ha ha1
  have hanc0 : 0 ≤ globalColumnAnchorDensity alpha := by
    unfold globalColumnAnchorDensity; positivity
  have hanc : globalColumnAnchorDensity alpha ≤ globalColumnQuadrupleDensity alpha := by
    unfold globalColumnAnchorDensity
    obtain ⟨u, hu⟩ : ∃ u, globalColumnWalkDensity alpha = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, globalColumnVertexDensity alpha = v := ⟨_, rfl⟩
    rw [hu] at hwalk0 hwalk1 hwalk ⊢
    rw [hv] at hvert0 hvert1 ⊢
    have h1 : u ^ 2 ≤ u := pow_le_of_le_one hwalk0 hwalk1 (by norm_num)
    have h2 : v ^ 3 ≤ 1 := pow_le_one₀ hvert0 hvert1
    have h3 := mul_le_mul h1 h2 (by positivity) hwalk0
    linarith
  have hword := (columnWordDensity_le hanc0 (hanc.trans hq1) hwalk0 hwalk1 k).2
  exact hword.trans (hanc.trans hq)

theorem one_le_columnSpectrumCap {beta : Real} (hb : 0 < beta) : 1 ≤ columnSpectrumCap beta :=
  Nat.ceil_pos.mpr (by positivity)

/-- **A rank of the form `⌈m·d/δ⌉` is exponential in the spectrum cap `d`.** -/
theorem thirteen_pow_le_rank_ceil {alpha m : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hm : 1 ≤ m) (k : Nat) :
    13 ^ columnSpectrumCap (columnEightDensity alpha) ≤
      ⌈(m * columnSpectrumCap (columnEightDensity alpha) : Real) /
        globalColumnWordDensity alpha k⌉₊ := by
  have hb := columnEightDensity_pos ha
  have hb1 := columnEightDensity_le_one ha ha1
  have hd : (1 : Real) ≤ columnSpectrumCap (columnEightDensity alpha) := by
    exact_mod_cast one_le_columnSpectrumCap hb
  have hδ0 := globalColumnWordDensity_pos ha ha1 k
  have hδ := (globalColumnWordDensity_le_witness ha ha1 k).trans (columnWitnessDensity_le hb hb1)
  obtain ⟨X, hX⟩ : ∃ X : Real, (13 : Real) ^ columnSpectrumCap (columnEightDensity alpha) = X :=
    ⟨_, rfl⟩
  have hXpos : 0 < X := by rw [← hX]; positivity
  rw [hX] at hδ
  have hmd : (1 : Real) ≤ m * columnSpectrumCap (columnEightDensity alpha) :=
    one_le_mul_of_one_le_of_one_le hm hd
  have hkey : X ≤ (m * columnSpectrumCap (columnEightDensity alpha) : Real) /
      globalColumnWordDensity alpha k := by
    rw [le_div_iff₀ hδ0]
    have h1 : X * globalColumnWordDensity alpha k ≤ X * (1 / X) :=
      mul_le_mul_of_nonneg_left hδ hXpos.le
    rw [mul_one_div_cancel hXpos.ne'] at h1
    linarith
  have hceil := Nat.le_ceil ((m * columnSpectrumCap (columnEightDensity alpha) : Real) /
      globalColumnWordDensity alpha k)
  have : ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) ≤
      (⌈(m * columnSpectrumCap (columnEightDensity alpha) : Real) /
        globalColumnWordDensity alpha k⌉₊ : Real) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, hX]
    exact hkey.trans hceil
  exact_mod_cast this

/-- **The model rank is exponential in the spectrum cap.** -/
theorem thirteen_pow_le_globalColumnModelRank {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    13 ^ columnSpectrumCap (columnEightDensity alpha) ≤ globalColumnModelRank alpha :=
  thirteen_pow_le_rank_ceil (m := 4) ha ha1 (by norm_num) 3

/-- With at least two cells per frequency, the test density is at most `2^(-g)`. -/
theorem modelTestDensity_le_inv_two_pow (g d : Nat) {r : Real} (hr : 0 < r) (hr1 : r ≤ 1) :
    modelTestDensity g d r ≤ 1 / 2 ^ g := by
  have hQ : (2 : Real) ≤ refinementCells (r / 2) := by
    have h : (2 : Real) ≤ 1 / (r / 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact h.trans (Nat.le_ceil _)
  have hp : (2 : Real) ^ g ≤ (refinementCells (r / 2) : Real) ^ (g + d) :=
    (pow_le_pow_left₀ (by norm_num) hQ g).trans
      (pow_le_pow_right₀ (by linarith) (Nat.le_add_right g d))
  unfold modelTestDensity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : Real) < 2 ^ g := by positivity
  linarith

theorem modelEliminationRounds_ge {beta : Real} (hb : 0 < beta) {M : Nat} (hM : 1 ≤ M) :
    Real.log 2 / beta ≤ modelEliminationRounds beta M := by
  unfold modelEliminationRounds
  refine le_trans ?_ (Nat.le_ceil _)
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.log_le_log (by norm_num)
  have : (1 : Real) ≤ M := by exact_mod_cast hM
  linarith

theorem globalColumnModelRadius_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    globalColumnModelRadius alpha k ≤ 1 := by
  have h := (globalColumnModelRadius_le ha ha1 k).trans (globalColumnIdentityRadius_le ha ha1)
  have hpi : (1 : Real) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  exact h.trans ((div_le_one (by positivity)).mpr hpi)

/-- **Model elimination loses doubly exponentially in the rank.** With test
density `β = modelTestDensity g d r`, any per-round divisor `m ≥ 1` and any
`v ∈ [0,1]`, the surviving density `(β/m)^t·v/2` after the prescribed
`t = modelEliminationRounds β M` rounds is at most `exp(-2^g/2)`. -/
theorem elimination_density_le {g d M : Nat} {r m v : Real} (hr : 0 < r) (hr1 : r ≤ 1)
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (modelTestDensity g d r / m) ^ modelEliminationRounds (modelTestDensity g d r) M * v / 2 ≤
      Real.exp (-(2 : Real) ^ g / 2) := by
  have hb0 := modelTestDensity_pos g d hr
  have hb1 := modelTestDensity_le_quarter g d hr
  have hbg := modelTestDensity_le_inv_two_pow g d hr hr1
  have ht := modelEliminationRounds_ge hb0 hM
  obtain ⟨β, hβ⟩ : ∃ β, modelTestDensity g d r = β := ⟨_, rfl⟩
  rw [hβ] at hb0 hb1 hbg ht ⊢
  obtain ⟨t, htt⟩ : ∃ t, modelEliminationRounds β M = t := ⟨_, rfl⟩
  rw [htt] at ht ⊢
  have hm0 : 0 < m := by linarith
  -- `t ≥ 2^g / 2`
  have hG : (0 : Real) < 2 ^ g := by positivity
  have hinv : (2 : Real) ^ g ≤ 1 / β := by
    rw [le_div_iff₀ hb0]
    have := mul_le_mul_of_nonneg_left hbg hG.le
    rw [mul_one_div_cancel hG.ne'] at this
    linarith
  have hlog : (1 / 2 : Real) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have ht2 : (2 : Real) ^ g / 2 ≤ t := by
    have h1 : Real.log 2 / β = Real.log 2 * (1 / β) := by ring
    have h2 : (2 : Real) ^ g / 2 ≤ Real.log 2 * (1 / β) := by
      have := mul_le_mul hlog hinv hG.le (by linarith)
      linarith
    linarith
  -- each round costs at least a factor `e`
  have hbase : β / m ≤ Real.exp (-1) := by
    have h1 : β / m ≤ β := div_le_self hb0.le hm
    have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    have h4 : (1 / 4 : Real) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) he
    linarith
  have hpow : (β / m) ^ t ≤ Real.exp (-(t : Real)) := by
    calc (β / m) ^ t ≤ (Real.exp (-1)) ^ t := pow_le_pow_left₀ (by positivity) hbase t
      _ = Real.exp (-(t : Real)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : Real.exp (-(t : Real)) ≤ Real.exp (-(2 : Real) ^ g / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hP : 0 ≤ (β / m) ^ t := by positivity
  calc (β / m) ^ t * v / 2 ≤ (β / m) ^ t * 1 := by nlinarith
    _ ≤ Real.exp (-(2 : Real) ^ g / 2) := by rw [mul_one]; exact hpow.trans hexp

/-- **The zero-core density is doubly exponentially small in the model rank.** -/
theorem globalColumnZeroDensity_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnZeroDensity alpha ≤
      Real.exp (-(2 : Real) ^ globalColumnModelRank alpha / 2) := by
  have hM : 1 ≤ globalColumnModelCount alpha := by
    have hδ0 := globalColumnWordDensity_pos ha ha1 3
    exact Nat.ceil_pos.mpr (by positivity)
  unfold globalColumnZeroDensity
  dsimp only
  exact elimination_density_le (globalColumnModelRadius_pos ha ha1 3)
    (globalColumnModelRadius_le_one ha ha1 3) hM (by norm_num)
    (globalColumnVertexDensity_pos ha ha1).le (globalColumnVertexDensity_le_one ha ha1)

theorem globalColumnAgreementSliceDensity_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnAgreementSliceDensity alpha ≤ 1 := by
  have hb := columnEightDensity_pos ha
  have hw1 := columnWitnessDensity_le_one hb (columnEightDensity_le_one ha ha1)
  have hs : 0 < globalColumnZeroRadius alpha / 2 :=
    div_pos (globalColumnZeroRadius_pos ha ha1) (by norm_num)
  have hQ : (1 : Real) ≤ refinementCells (globalColumnZeroRadius alpha / 2) := by
    exact_mod_cast (show 0 < refinementCells (globalColumnZeroRadius alpha / 2) from
      Nat.ceil_pos.mpr (by positivity))
  unfold globalColumnAgreementSliceDensity
  exact (div_le_of_le_mul₀ (by positivity) zero_le_one
    (hw1.trans (by rw [one_mul]; exact one_le_pow₀ hQ)))

/-- **The guaranteed agreement density is triple-exponentially small.** -/
theorem globalColumnAgreementDensity_le_triple_exp {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnAgreementDensity alpha ≤
      Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2) := by
  have hz := globalColumnZeroDensity_le ha ha1
  have hz0 := globalColumnZeroDensity_pos ha ha1
  have hs0 := globalColumnAgreementSliceDensity_pos ha ha1
  have hs1 := globalColumnAgreementSliceDensity_le_one ha ha1
  have hg := thirteen_pow_le_globalColumnModelRank ha ha1
  have hpow : (2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) ≤
      (2 : Real) ^ globalColumnModelRank alpha := pow_le_pow_right₀ (by norm_num) hg
  have hexp := Real.exp_le_exp.mpr (show -(2 : Real) ^ globalColumnModelRank alpha / 2 ≤
      -(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2 by linarith)
  unfold globalColumnAgreementDensity
  have hsq : (globalColumnAgreementSliceDensity alpha) ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  calc globalColumnZeroDensity alpha * globalColumnAgreementSliceDensity alpha ^ 2
      ≤ globalColumnZeroDensity alpha * 1 := mul_le_mul_of_nonneg_left hsq hz0.le
    _ ≤ _ := by rw [mul_one]; exact hz.trans hexp

/-- `2·d^(2^64) < 2^(13^d)` once `d ≥ 64`. -/
theorem two_mul_pow_lt_two_pow_thirteen_pow {d : Nat} (hd : 64 ≤ d) :
    2 * d ^ (2 ^ 64) < 2 ^ (13 ^ d) := by
  obtain ⟨X, hX⟩ : ∃ X : Nat, 2 ^ 64 = X := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [← hX]; exact Nat.one_le_two_pow
  have h1 : d ^ X < (2 ^ d) ^ X :=
    Nat.pow_lt_pow_left (Nat.lt_of_succ_le (succ_le_two_pow d)) (by omega)
  rw [← pow_mul] at h1
  have h2 : 2 * d ^ X < 2 ^ (d * X + 1) := by rw [pow_succ]; omega
  -- `d·X + 1 ≤ 2^(3d) ≤ 13^d`
  have h3 : 2 * X ≤ 2 ^ (2 * d) := by
    have : 2 ^ 65 ≤ 2 ^ (2 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h65 : 2 ^ 65 = 2 * X := by rw [← hX]; norm_num
    omega
  have h4 : d * X + 1 ≤ 2 ^ (3 * d) := by
    have hd1 := succ_le_two_pow d
    have hsplit : 2 ^ (3 * d) = 2 ^ (2 * d) * 2 ^ d := by rw [← pow_add]; congr 1; omega
    rw [hsplit]
    calc d * X + 1 ≤ (2 * X) * (d + 1) := by nlinarith
      _ ≤ 2 ^ (2 * d) * 2 ^ d := Nat.mul_le_mul h3 hd1
  have h5 : 2 ^ (3 * d) ≤ 13 ^ d := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) d
  have h6 : 2 ^ (d * X + 1) ≤ 2 ^ (13 ^ d) := Nat.pow_le_pow_right (by norm_num) (h4.trans h5)
  rw [hX]
  exact lt_of_lt_of_le h2 h6

/-- **A triple-exponential bound defeats every polynomial contract.** Anything
at most `exp(-2^(13^d)/2)` is below `exp(-(4/alpha)^K)` for `alpha ≤ 1/2` and
`K ≤ 2^64`. -/
theorem lt_polynomial_contract_of_le_triple_exp {alpha x : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) {K : Nat} (hK : K ≤ 2 ^ 64)
    (htri : x ≤ Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2)) :
    x < Real.exp (-(4 / alpha) ^ K) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨d, hdd⟩ : ∃ d, columnSpectrumCap (columnEightDensity alpha) = d := ⟨_, rfl⟩
  rw [hdd] at htri
  -- `d ≥ 64/alpha^2 = 4y^2` with `y = 4/alpha ≥ 8`
  have hb := columnEightDensity_pos ha
  have hbh := columnEightDensity_le_half ha ha1
  have hy8 : (8 : Real) ≤ 4 / alpha := by rw [le_div_iff₀ ha]; linarith
  have hdy : (4 / alpha) * (4 / alpha) * 4 ≤ (d : Real) := by
    have hc : 16 / (columnEightDensity alpha) ^ 2 ≤ (d : Real) := by
      rw [← hdd]; exact Nat.le_ceil _
    have hsq : (columnEightDensity alpha) ^ 2 ≤ (alpha / 2) ^ 2 :=
      pow_le_pow_left₀ hb.le hbh 2
    have h16 : 16 / (alpha / 2) ^ 2 ≤ 16 / (columnEightDensity alpha) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    have he : 16 / (alpha / 2) ^ 2 = (4 / alpha) * (4 / alpha) * 4 := by
      field_simp; ring
    linarith
  obtain ⟨y, hy⟩ : ∃ y, 4 / alpha = y := ⟨_, rfl⟩
  rw [hy] at hy8 hdy ⊢
  have hyd : y ≤ (d : Real) := by nlinarith
  have hd64 : (64 : Real) ≤ d := by nlinarith
  have hd64n : 64 ≤ d := by exact_mod_cast hd64
  -- `y^K ≤ d^(2^64) < 2^(13^d)/2`
  have hyK : y ^ K ≤ (d : Real) ^ (2 ^ 64) :=
    (pow_le_pow_right₀ (by linarith) hK).trans (pow_le_pow_left₀ (by linarith) hyd _)
  have hnat := two_mul_pow_lt_two_pow_thirteen_pow hd64n
  have hreal : 2 * (d : Real) ^ (2 ^ 64) < (2 : Real) ^ (13 ^ d) := by exact_mod_cast hnat
  have hlt : -(2 : Real) ^ (13 ^ d) / 2 < -y ^ K := by linarith
  exact htri.trans_lt (Real.exp_lt_exp.mpr hlt)

/-- **The zero-core chain cannot supply a polynomial deep-structure bound.**
For `alpha ≤ 1/2` and `K ≤ 2^64`, the guaranteed agreement density is below
`exp(-(4/alpha)^K)`, the agreement `DeepStructureAt Bnd` requires at density
`alpha` once `Bnd alpha ≤ (4/alpha)^K`. -/
theorem globalColumnAgreementDensity_lt_polynomial_contract {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) {K : Nat} (hK : K ≤ 2 ^ 64) :
    globalColumnAgreementDensity alpha < Real.exp (-(4 / alpha) ^ K) :=
  lt_polynomial_contract_of_le_triple_exp ha ha2 hK
    (globalColumnAgreementDensity_le_triple_exp ha (by linarith))

end LeanProofs.GowersSzemeredi
