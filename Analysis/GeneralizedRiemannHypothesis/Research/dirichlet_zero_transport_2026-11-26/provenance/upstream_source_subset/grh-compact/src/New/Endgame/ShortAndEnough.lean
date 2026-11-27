import New.Columns.LocalStatement
import New.Rows.RowVolume
import New.Seesaw.SeesawTheorem

/-! Choice of the level prime. The level is a prime N, found in a short window, whose logarithm is
within a small error of the total excess of the lifts' size over their expected divisibility, per
unit of order. This standard choice of data by an explicit formula makes the level pay these
excesses, so the size bound for the chain is the main amount minus the prime sum, up to a small
error.

Part of: The inequality (⋆): upper bound for weighted non-split primes (see New.Main).

This file: Theorem A (`Data.short_forms`: projected Poincaré series of integral forms have small
lifts and small index), Theorem B (`Data.enough_forms`: few translates nearly span), the remainder
as prime sums. N itself is `Data.N` (New.Seesaw.IndexTypes). -/

open Finset Module Parameters Real Stirling Submodule LevelPlaces.LevelForm

/-- For a finite set T of primes and integers g_l vanishing outside T, there is a rational q > 0
with log q = ∑_{l∈T} g_l log l and l-adic absolute value |l|^{g_l} at every prime l. -/
lemma exists_rat_log_eq_and_padic_norm_eq T (g : ℕ → ℤ) (hT : ∀ l ∈ T, l.Prime) (h : ∀ l ∉ T,
  g l = 0) : ∃ q : ℚ, 0 < q ∧ log q = ∑ l ∈ T, g l * log l ∧
  ∀ l [Fact l.Prime], ‖(q : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ g l := ⟨∏ l ∈ T, l ^ g l, by
  simp (disch := grind [zpow_pos, Nat.Prime.pos, Nat.cast_pos]) [log_prod, prod_pos]
  grind [prod_eq_single, Nat.coprime_primes, _root_.Nat.Coprime.norm_natCast_eq_one, one_zpow,
    zpow_zero, Fact]⟩

variable {P} (D : Data P)

/-- The main term h_main = m·k·𝖴 of the height, with 𝖴 = `Data.dirCost` the cost of one
direction. -/
noncomputable def Data.mainHeight := D.m * D.k * D.dirCost

/-- The number a(log a − 1 − ℓ − w̄), ℓ = `chowlaSelbergConst` d, w̄ the mean of log w(τ) over the
infinite places τ and w = `Data.nominalWeight`. -/
noncomputable def Data.mainAsk :=
  D.a * (log D.a - 1 - chowlaSelbergConst P.d - (∑ τ, (D.nominalWeight τ).log) / D.f)

/-- The remainder rem: the sum over the tops τ of the differences Ask(a, τ) − `Data.mainAsk`, with
Ask =
`Data.primeSum`. -/
noncomputable def Data.remainder := ∑ τ ∈ D.tops, (D.primeSum D.a τ - D.mainAsk)

/-- The height per row h₀ = `Data.heightPerRow` is at most h_main − m·rem + fa log³ b, with
h_main = `Data.mainHeight` and rem = `Data.remainder`.

Choice of the level prime. -/
lemma Data.heightPerRow_le : D.heightPerRow ≤ D.mainHeight - D.m * D.remainder + D.budget := by
  set w := (∑ τ, (D.nominalWeight τ).log) / D.f
  set G := (D.gProd * D.rootDisc / (2 * π)).log with hG
  have stirling : log D.a.factorial ≤ D.a * log D.a - D.a + (1 + log D.a / 2) := by
    have S := log_stirlingSeq'_antitone D.a.pred.zero_le
    simp [log_stirlingSeq_formula, log_div, log_mul, log_sqrt, (HasLogBound.pos D).ne',
      (D.nat_le_of_hasLogBound : 1 ≤ D.a)] at S
    bound
  have excess : D.jetSize D.a - D.mainAsk ≤ D.a * (w + G) + (1 + log D.a / 2) := by
    simp [jetSize, mainAsk, hG, bigOmega, log_div, log_mul, (HasLogBound.pos D).ne']
    bound
  -- the left side is `logLevelTarget`
  have level : D.m * (w + G) - (G + 15 / 2 * D.logB) ≤
    log D.N := by grind [D.log_N_mem_window.1, logLevelTarget]
  calc D.heightPerRow = D.mainHeight - D.m * D.remainder + #_ *
      (D.m * (D.jetSize D.a - D.mainAsk) - D.a * log D.N) := by
        simp [heightPerRow, mainHeight, remainder]
        ring
    _ ≤ D.mainHeight - D.m * D.remainder + #D.tops * (D.m * (_ + (1 + log D.a / 2)) -
        D.a * (_ - (G + _))) := by bound
    -- `m a (w + G)` cancels
    _ = _ + #D.tops * (D.m * (1 + log D.a / 2) + D.a * (G + 15 / 2 * D.logB)) := by ring
    _ ≤ _ := add_le_add_right D.le_of_hasLogBound _

/-- Crude bound: |h_main| + m·|rem| ≤ b² x⁹⁹, with h_main = `Data.mainHeight` and rem =
`Data.remainder`. -/
lemma Data.abs_mainHeight_add_remainder_le : |D.mainHeight| + D.m * |D.remainder| ≤
  D.b ^ 2 * D.x ^ 99 := by
  have := D.hasLogUpper_of_abs_le (by grind [c, sum_nonneg] : |chowlaSelbergConst P.d| ≤ P.c)
  -- `|λ(ν)| ≤ 2ν` bounds the asks
  have {σ y l} [h : D.HasLogUpper (D.a * (2 * y)) l] : D.HasLogUpper (D.primeSum y σ) l :=
    ⟨h.1.trans' (by grw [primeSum, abs_sum_le_sum_abs, sum_le_card_nsmul _ _ |2 *
    y|] <;> simp [posPart, abs_of_nonneg]; grw [(lambdaClass_nonneg_and_abs_le ..).2,
    ← nominalWeight_nonneg, le_abs_self y]; simp_all [field])⟩
  simpa [mainHeight, dirCost, remainder, mainAsk, jetSize] using D.le_of_hasLogBound

/-- The remainder in terms of prime sums: rem = a·(#thick·(R_{N₀}(x) − R_{N₀}(x₁)) +
#tops·R₁(x₁)), where R_M = `primeError` and #thick, #tops count the thick places and the tops. -/
lemma Data.remainder_eq : D.remainder = D.a * (#D.thick *
  (primeError P.d P.N₀ D.x - primeError P.d P.N₀ D.x₁) + #D.tops * primeError P.d 1 D.x₁) := by
  -- as `τ` runs over the tops, `-ν τ` meets every thick place if `ν ≡ 1 mod N₀`, and none otherwise
  have A (ν : ℕ) b : #{τ ∈ D.tops | D.placeOfInt (-ν) * τ ∈ D.thick} * (lambdaClass P.d 1 ν * b) =
      #D.thick * (lambdaClass P.d P.N₀ ν * b) := by
    rw [card_filter, tops, sum_filter, ← (Equiv.divRight (D.placeOfInt (-ν))).sum_comp]
    simp +contextual [← sum_filter, lambdaClass, filter_inter, Unique.eq_default,
      placeClass_of_thick, @eq_comm _ˣ (-1), apply_ite card, div_eq_one, Set.indicator]
  -- the prime sums are remainders plus main terms (`primeError_eq_sum`; the constant for modulus
  -- `1` is `-1 - chowlaSelbergConst` by `re_logDerivMean_one`, the one for `N₀` drops out of the
  -- difference)
  have asks : ∑ τ ∈ D.tops, D.primeSum D.a τ = D.a * (#D.thick * (primeError P.d P.N₀ D.x -
    primeError P.d P.N₀ D.x₁) + #D.tops * primeError P.d 1 D.x₁ + (#D.thick *
    ((D.logX - D.logX₁) / P.N₀.totient) + #D.tops * (D.logX₁ - 1 - chowlaSelbergConst P.d))) := by
    simp [A, @sum_ite D.Φ, filter_not, cast_card_sdiff, sub_mul, re_logDerivMean_one, ← mul_sum,
      primeSum, nominalWeight, D.tops.sum_comm, primeError_eq_sum D.a D.logX₁.exp_pos
      D.le_of_hasLogBound, primeError_eq_sum D.a D.logX.exp_pos D.le_of_hasLogBound, div_ite,
      sub_ite, apply_ite posPart, ← sum_div]
    field [(HasLogBound.pos D).ne']
  -- `mainAsk` is the mean of the same main terms, as `f = #tops φ(N₀)`
  have main : #D.tops * D.mainAsk = D.a * (#D.thick * ((D.logX - D.logX₁) / P.N₀.totient) +
      #D.tops * (D.logX₁ - 1 - chowlaSelbergConst P.d)) := by
    simp [mainAsk, nominalWeight, apply_ite, log_div, (HasLogBound.pos D).ne', sum_ite, filter_not,
      cast_card_sdiff, card_infinitePlace_E, show #D.tops = _ by apply card_placeClass_eq]
    field [(HasLogBound.pos D).ne']
  simp [*, remainder]
  ring

/-- The map i_N from the ramified columns to the columns: the inclusion times the non-zero
constant chosen from the seesaw identity `Data.seesaw`. -/
noncomputable def Data.scaledInclusion := D.seesaw.choose.1 • D.ramifiedColumns.subtype

/-- For s in the finite group 𝖦, the linear map |𝖦|·e₀ s P i_N from the ramified columns to the
rows, P the Poincaré series `Data.poincare`. -/
noncomputable abbrev Data.projectedPoincare (s : D.G) : D.ramifiedColumns →ₗ[ℂ] D.rows :=
  D.goodProjTranslate s ∘ₗ D.poincare ∘ₗ D.scaledInclusion

/-- The set of ramified columns that are integral (`integralFormsAt` with d = 1) at every place ι
above l, for every prime l. -/
abbrev Data.integralRamified :=
  {φ : D.ramifiedColumns | ∀ l [Fact l.Prime] [PadicPlace l], φ.1.1 ∈ integralFormsAt D.Column 1}

/-- Index at most δ: some e has ∑_{l∈U} e_l ≤ δ for all finite U; for ι above l, ϑ prime to l, an
O_ι-matrix u with |det u| ≥ exp(−e_l) turns y into rows with ι-integral lifts `Data.Θ`. -/
def Data.IndexLe {n} (y : Fin n → D.rows) δ := ∃ e : ℕ → ℝ, (∀ U, ∑ l ∈ U, e l ≤ δ) ∧
  ∀ l [Fact l.Prime] (ι : PadicPlace l) ϑ, l.Coprime ϑ.levelNorm → ∃ u :
  Matrix _ _ embValRing, (-e l).exp ≤ ‖ιₚ u.det‖ ∧ ∀ i, D.Θ ϑ (∑ k, u i k • y k) ∈ integralForms ι

/-- Short forms: for some rational q > 0 and B_s = q·`Data.projectedPoincare` s, (a) the φ in
`Data.integralRamified` with ‖Θ₁B_sφ‖²_σ ≤ exp(h_main − m·rem + 𝓑 log b) for all s, σ span the
ramified columns; (b) for t ⊆ 𝖦, every finite family in ⋃_{s∈t} B_s(`Data.integralRamified`) has
index (`Data.IndexLe`) at most |t|·dim(columns)·𝓑, where 𝓑 = `Data.budget`. -/
lemma Data.short_forms : ∃ q > (0 : ℚ), ∃ B, B = (q : ℂ) • D.projectedPoincare ∧ (∃ S ⊆
  D.integralRamified, span ℂ S = ⊤ ∧ ∀ φ ∈ S, ∀ s σ, (D.Θ 1 (B s φ)).normSqAt σ ≤ exp (D.mainHeight
  - D.m * D.remainder + D.logB * D.budget)) ∧ ∀ (t : Finset D.G) n (y : Fin n → _), (∀ i, y i ∈
  Set.image2 (B ·) t D.integralRamified) → D.IndexLe y (#t * finrank ℂ D.Column * D.budget) := by
  -- `q` divides out the gains, less the allowed losses
  obtain ⟨q, q0, e, v⟩ := exists_rat_log_eq_and_padic_norm_eq (D.nonsplitPrimes ∪ {D.N})
    (fun l ↦ ⌊D.allowedLoss l - ite (l ∈ D.nonsplitPrimes)
    (D.gain l) 0⌋) (by grind [N_prime]) (by grind [allowedLoss, Int.floor_zero])
  choose Ψ G S using D.seesaw.choose_spec
  refine ⟨q, q0, _, rfl, ⟨_, fun φ k l _ _ ↦ ⟨φ.1.2, k.1 l⟩, D.span_short_ramifiedColumns,
    fun φ k s σ ↦ (map_smul (D.projectedPoincare s) .. ▸ normSqAt_goodProjTranslate_le
    (S .. ▸ weylNormSq_Bmu_le (B := 2 * log q + D.budget)
    (G 1) (by simpa [two_mul, exp_add, exp_log, q0, sq] using k.2 σ ·) ·)).trans (by
    grw [e, heightPerRow_le, Int.floor_le]
    simp [sub_mul, -mem_filter, -union_singleton]
    grw [sum_allowedLoss_mul_log_le]; ring; simpa using D.le_of_hasLogBound)⟩, fun t n y h ↦
    ⟨fun l ↦ #t * finrank ℂ D.Column * (_ * log l),
    fun U ↦ by grw [← mul_sum, sum_allowedLoss_mul_log_le], fun l _ ι ϑ c ↦
    (exists_indexDvd_Bmu_divisible (Int.ceil_lt_add_one _)).elim fun n a ↦ a.2.elim fun _ b ↦
    (IndexDvd.sup (N' := (integralForms ι).comap ((D.Θ ϑ).restrictScalars embValRing)) (f :=
    ((q : ℂ) • D.projectedPoincare · |>.restrictScalars embValRing)) (fun s ↦ b.1.comap
    (D.ramifiedColumns.subtype.restrictScalars _) le_rfl fun φ _ h ↦ congr($((D.Θ ϑ).map_smul ..) ∈
    integralForms ι).mpr (goodProjTranslate_mem_integralForms ι (fun g ↦ by
    erw [weylGauge_smul, congr($(S ..).1 g)]
    simpa [v, weylGauge_smul, ← Int.floor_neg] using (b.2 _ _ (G ϑ) c _ h φ.2).2 g) s)) t _ y
    fun k ↦ subset_span (.inl (Set.image2_subset_left (by exact fun _ ↦ (· l)) (h k)))).imp
    fun u ⟨k, h⟩ ↦ ⟨?_, h⟩⟩⟩
  · apply (Valuation.valuationSubring.integers _).le_of_dvd at k
    simp [norm_p_eq_inv, ← NNReal.coe_le_coe] at k
    grw [← k, ← le_log_iff_exp_le] <;> simp [NeZero.pos]
    linarith [mul_le_mul_of_nonneg_right a.1 (mul_nonneg (#t).cast_nonneg (log_natCast_nonneg l))]

/-- Enough forms: columns and rows are non-zero, and for some set t ⊂ 𝖦 with #t·dim(columns) ≤
5D log(1 + b²), D = dim(rows), the images of the maps `Data.projectedPoincare` s, s ∈ t, span
dimension at least (1 − 4/b²)D. -/
lemma Data.enough_forms : 0 < finrank ℂ D.Column ∧ 0 < D.rowDim ∧
  ∃ t, #t * finrank ℂ D.Column ≤ 5 * D.rowDim * log (1 + D.b ^ 2) ∧ (1 - 4 / D.b ^ 2) * D.rowDim ≤
  finrank ℂ ↥(⨆ s ∈ t, (D.projectedPoincare s).range) := have := D.columnCoords.nontrivial
  ⟨finrank_pos, D.finrank_rows_ne_zero.pos, (exists_few_translates (W :=
    D.rows) (HasLogBound.pos D) (D.ramifiedColumns_fill_rows _)).imp fun _ ↦ .imp (by simp)
    (·.trans (mod_cast finrank_mono (iSup₂_mono fun _ _ _ ⟨φ, e⟩ ↦ ⟨⟨_, φ, rfl⟩, e⟩)))⟩
