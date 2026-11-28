import New.Reduction.PrimeSums
import New.Spanning.Unfolding.FillingAdmissible
import New.UpperBound.Divisibility.ChainDatumExpansion
import New.UpperBound.Objects.RowChain
import New.UpperBound.Size.Estimates

/-!
# Archimedean size of the composite lift, and passage to target forms by the good projection

The composite lift of a chain datum is `New.Data.restrictedChain` of the expansion of its glued
tensor, so its size (`New.Data.weylNormSq_compositeLift_le`) follows from the bound for
`New.Data.restrictedChain`. This map sends source forms (algebraic forms on `X_0`) to forms on
`Y_m`. Separately, a form `z` of principal level on `Y₀` (the side of the target forms) is replaced
by its good part `|𝖦| e₀ s z`. For the lift to `Y_m` (`lowerChainAtLevel`), this replacement keeps
integrality of any scalar multiple `c •` of it, and it enlarges the bound `exp B` on its values to a
bound `exp (x ^ 99 + B)` on the class sum.

## Main definitions and results

* `New.Data.rowSizeSum`, `New.Data.chainSize`: the size of the rows of one lift diagram, and the
  main term of the size of the chain.
* `New.Data.weylNormSq_restrictedChain_le`, `New.Data.weylNormSq_compositeLift_le`: the size bounds
  for the restricted chain and for the composite lift.
* `New.Data.lowerChain_goodProjTranslate_apply`: the lift of `|𝖦| e₀ s z` is a combination of right
  translates of the lift of `z`, with the coefficients of `|𝖦| e₀`.

Notions from other files:
* `New.Data.jetSize`: The size `s_∞(j) = log j! + j log (M / Ω)` of a derivative of order `j`.
* `New.Data.restrictedChain`: For coefficients `Ψ` on translations of the integral vacuum, the
  combination of the chains of `m` lifts of these translates, restricted to `Y_m`. `Ψ` is a weak
  chain datum (`New.Data.IsWeakChainDatum`) if the combined tensor is invariant and the coefficients
  are admissible.
* `New.Data.gain`: The divisibility at a prime `p` that is asked of the chain.
* `New.LevelPlaces.LevelForm.integralForms`: The forms φ whose value φ(g) has gauge `New.weylGauge`
  at most 1 for every g.
* `New.LevelPlaces.LevelForm.normSqAt`: The class sum of the squared Gram norms `New.weylNormSq` of
  the vectors σ(φ(g)).

## Relation to the literature

The untwisted chain of lifts enlarges squared norms of all conjugates by at most an explicit factor,
which gives the size side of the product formula. Related work on algebraic modular forms as values
on lattice classes: Gross, Algebraic modular forms, 1999; Greenberg–Voight, Lattice methods for
algebraic modular forms on classical groups, 2014.
-/

/-!
## Archimedean size bound for the composite of theta lifts on source forms

The map `New.Data.restrictedChain` is a combination, with coefficients `Ψ`, of chains of `m` theta
lifts `X_0 → X_1 → … → X_m`, followed by the restriction `New.Data.restrictToY` to `Y_m`. The proof
of `New.Data.weylNormSq_restrictedChain_le` multiplies four bounds: those for the single lifts
(`New.Parameters.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination`), the class numbers, the size
of the coefficients and the bound for the restriction.
-/

section SizeBound

open Finset Real

namespace New.Data

open Parameters Stirling

/-! ### The level compensates the excess -/

/-- The excess of one lift: `s_∞(a) - s_main ≤ a log (κ̄ M rd_E / 2π) + 1 + (log a) / 2`. Here
`a = D.a` is the product `x b` of the integer scales `x` and `b` of the data `D`, `M = D.M` is the
product of the two primes of the principal level, `rd_E` is the root discriminant of the CM field
`E = D.E`, and `log κ̄` is the mean of `log κ(τ)`, with `κ = D.weight`, over the set `D.Φ` of the
`f = D.f` infinite places of `E`. Further `s_∞(a) = D.jetSize a = log a! + a log (M / Ω)`, with the
period `Ω = P.bigOmega D.towerExp`, and `s_main = D.mainPrimeSum = a (log (a / κ̄) + c₁)`, with `c₁`
the real part of `logDerivMean P.d 1 1`. -/
lemma jetSize_sub_mainPrimeSum_le {P : Parameters} (D : Data P) :
    D.jetSize D.a - D.mainPrimeSum ≤
      D.a * ((∑ τ : D.Φ, log (D.weight τ)) / D.f + log (D.M * D.rootDisc / (2 * Real.pi))) +
        (1 + log D.a / 2) := by
  have stirling : log D.a.factorial ≤ D.a * log D.a - D.a + (1 + log D.a / 2) := by
    have ha : 1 ≤ D.a := D.nat_le_of_hasLogBound
    have h_seq : log D.a.factorial ≤
        1 - log 2 / 2 + D.a * (log D.a - 1) + 2⁻¹ * (log 2 + log D.a) := by
      -- The logarithm of the Stirling sequence is antitone, so it is at most its value at `1`.
      simpa [log_stirlingSeq_formula, log_div, log_mul, log_sqrt, (HasLogBound.pos D).ne', ha]
        using log_stirlingSeq'_antitone D.a.pred.zero_le
    linarith
  -- We have `log Ω = -1 - c₁ + log (2π / rd_E)`, with `c₁` the real part of `logDerivMean P.d 1 1`.
  have period : log (D.M / P.bigOmega D.towerExp) =
      1 + (logDerivMean P.d 1 1).re + log (D.M * D.rootDisc / (2 * Real.pi)) := by
    rw [re_logDerivMean_one, bigOmega]
    -- Expand both logarithms; the terms in `c₁`, `M`, `π` and `rd_E` agree.
    simp [log_div, log_mul, (HasLogBound.pos D).ne']
    ring
  -- The constant `c₁` cancels.
  rw [jetSize, mainPrimeSum, period]
  linarith

/-- The level compensates the excess of the `m` lifts:
`m (s_∞(a) - s_main) - a log N ≤ 32 a log b`. Here `m = D.m` is the number of theta lifts in the
chain, `a = D.a` is the product `x b` of the integer scales `x` and `b` of the data `D`,
`log b = D.logB`, and the level `N = D.N` is a prime. Further
`s_∞(a) = D.jetSize a = log a! + a log (M / Ω)`, with `M = D.M` the product of the two primes of the
principal level and `Ω` the period `New.Parameters.bigOmega` of the field `D.E`, and
`s_main = D.mainPrimeSum` is the expected mean of the prime sums `D.primeSum a τ` over the infinite
places `τ ∈ D.aPlaces`. -/
lemma mul_jetSize_sub_mainPrimeSum_sub_le {P : Parameters} (D : Data P) :
    D.m * (D.jetSize D.a - D.mainPrimeSum) - D.a * log D.N ≤ 32 * (D.a * D.logB) := by
  set w : ℝ := (∑ τ : D.Φ, log (D.weight τ)) / D.f
  set G : ℝ := log (D.M * D.rootDisc / (2 * Real.pi))
  -- The lower end of the window for `log N`.
  have level : D.m * (w + G) - (G + 15 / 2 * D.logB) ≤ log D.N := by
    grw [← D.log_N_mem_Icc_logLevelTarget.1, logLevelTarget]
    linarith
  have h_stirling : D.m * (1 + log D.a / 2) ≤ D.a * D.logB := D.le_of_hasLogBound
  have h_size : G ≤ 23 * D.logB := le_of_abs_le D.abs_log_M_mul_rootDisc_le
  have h_log : 0 ≤ D.logB := (HasLogBound.pos D).le
  calc D.m * (D.jetSize D.a - D.mainPrimeSum) - D.a * log D.N
      ≤ D.m * (D.a * (w + G) + (1 + log D.a / 2)) -
          D.a * (D.m * (w + G) - (G + 15 / 2 * D.logB)) := by
        grw [D.jetSize_sub_mainPrimeSum_le, ← level]
    -- The terms `m a (w + G)` cancel.
    _ = D.m * (1 + log D.a / 2) + D.a * (G + 15 / 2 * D.logB) := by ring
    _ ≤ D.a * D.logB + D.a * (23 * D.logB + 8 * D.logB) := by
        grw [h_stirling, h_size, show (15 / 2 : ℝ) ≤ 8 by norm_num]
    _ = 32 * (D.a * D.logB) := by ring

/-- The level compensates the excess at all `a`-places together:
`#Φ_a (m (s_∞(a) - s_main) - a log N) ≤ 32 f a log b`. Here `Φ_a = D.aPlaces` is a set of infinite
places of `D.E`, `f = D.f` is the number of all infinite places, `s_∞ = D.jetSize` and
`s_main = D.mainPrimeSum`. -/
lemma card_aPlaces_mul_excess_le {P : Parameters} (D : Data P) :
    #D.aPlaces * (D.m * (D.jetSize D.a - D.mainPrimeSum) - D.a * log D.N) ≤
      32 * (D.f * D.a * D.logB) := by
  have h_log : 0 ≤ D.logB := (HasLogBound.pos D).le
  grw [mul_jetSize_sub_mainPrimeSum_sub_le, show #D.aPlaces ≤ D.f from card_le_univ _]
  linarith

/-! ### The exponent in the size bound -/

/-- The gains add up to the prime sums: over the primes `p < x₁` that do not split in
`K = ℚ(√-d)`, with `d = P.d` and the cut-off `x₁ = D.x₁`,
`2 ∑ gain_p log p = m ∑_{τ ∈ Φ_a} s_fin(a, τ) + m k ∑_τ s_fin(κ(τ), τ)`. Here `gain_p = D.gain p` is
the divisibility at `p` asked of the chain of `m = D.m` theta lifts, `k = D.k` is the rank of the
source of the chain, `κ(τ) = D.weight τ` is the weight at the infinite place `τ` of `D.E`, and
`Φ_a = D.aPlaces` is the set of places `≡ 1` modulo `P.q₀`. The prime sum `D.primeSum y τ` is
`s_fin(y, τ) = ∑_{1 ≤ ν ≤ a} Λ(ν) (1 - χ_K(ν)) (y / ν - κ(-ν τ))₊`, with `a = D.a`. -/
lemma two_mul_sum_gain_mul_log {P : Parameters} (D : Data P) :
    2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p =
      D.m * ∑ τ ∈ D.aPlaces, D.primeSum D.a τ +
        D.m * D.k * ∑ τ : D.Φ, D.primeSum (D.weight τ) τ := by
  -- The gain is zero at split primes, so the sum may run over all primes below `x₁`.
  have h_primes : ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p =
      ∑ p ∈ range ⌈D.x₁⌉₊ with p.Prime, D.gain p * log p := by
    rw [smallNonsplitPrimes, ← filter_filter]
    exact sum_filter_of_ne fun p _ h_ne h_split ↦ h_ne (by simp [D.gain_eq_zero (Or.inl h_split)])
  -- Each prime sum is the sum of its local terms over the same primes.
  have h_aPlaces : ∑ τ ∈ D.aPlaces, D.primeSum D.a τ =
      ∑ p ∈ range ⌈D.x₁⌉₊ with p.Prime, ∑ τ ∈ D.aPlaces, 2 * D.localPrimeSum p D.a τ * log p :=
    (sum_congr rfl fun τ _ ↦ D.primeSum_eq_sum_localPrimeSum le_rfl τ le_rfl).trans sum_comm
  have h_allPlaces : ∑ τ : D.Φ, D.primeSum (D.weight τ) τ =
      ∑ p ∈ range ⌈D.x₁⌉₊ with p.Prime,
        ∑ τ : D.Φ, 2 * D.localPrimeSum p (D.weight τ) τ * log p :=
    (sum_congr rfl fun τ _ ↦
      D.primeSum_eq_sum_localPrimeSum le_rfl τ D.le_of_hasLogBound).trans sum_comm
  rw [h_primes, h_aPlaces, h_allPlaces, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  simp only [gain, localPrimeSumTotal, ← sum_mul, ← mul_sum]
  ring

/-- The prime sums cancel in the exponent of the size bound:
`h_main - m rem + 2 ∑ gain_p log p = m #Φ_a s_main + m k ∑_τ s_∞(κ(τ))`. Write `s_∞ = D.jetSize` for
the size `log j! + j log (M / Ω)` of a derivative of order `j`, `s_fin = D.primeSum` for the prime
sums, `s_main = D.mainPrimeSum` for the expected mean of `s_fin(a, τ)` over `τ ∈ Φ_a = D.aPlaces`,
and `κ(τ) = D.weight τ` for the weight at an infinite place `τ`. Then the main amount is
`h_main = m k ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))`, with `m` the number of lifts and `k` the rank of
the source, the total remainder is `rem = ∑_{τ ∈ Φ_a} (s_fin(a, τ) - s_main)`, and
`gain_p = D.gain p` is the divisibility asked at a prime `p < x₁` that does not split in
`ℚ(√-d)`. -/
lemma mainAmount_sub_add_two_mul_sum_gain {P : Parameters} (D : Data P) :
    D.mainAmount - D.m * D.totalRemainder + 2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p =
      D.m * #D.aPlaces * D.mainPrimeSum + D.m * D.k * ∑ τ : D.Φ, D.jetSize (D.weight τ) := by
  simp only [two_mul_sum_gain_mul_log, mainAmount, directionAmount, totalRemainder, sum_sub_distrib,
    sum_const, nsmul_eq_mul]
  ring

/-! ### One kernel -/

/-- For row `i` of the Young diagram of the weight of a lift at the infinite place `τ`, the main
length plus the slack is at most `2 a`, where `a = D.a` is the product `x b` of two scales. The main
length is `a` or `0` for `i = 0`, the weight `D.weight τ` for `0 < i < D.k`, and `0` otherwise; the
slack is the number of boxes by which the row may exceed its main length. -/
lemma rowMainLength_add_rowSlack_le {P : Parameters} (D : Data P) (τ : D.Φ) (i : ℕ) :
    D.rowMainLength τ i + D.rowSlack i ≤ 2 * D.a := by
  have h_slack : D.natB + D.offWeight + D.halfGap ^ 2 ≤ D.a := D.nat_le_of_hasLogBound
  have h_weight : D.weight τ ≤ D.natB + D.offWeight := D.weight_le_natB_add_offWeight τ
  -- Both the main length and the slack are at most `a`.
  have h_main_le : D.rowMainLength τ i ≤ D.a := by
    rw [rowMainLength, columnCount_one, firstRowExcess]
    split_ifs <;> omega
  have h_slack_le : D.rowSlack i ≤ D.a := by
    rw [rowSlack]
    split_ifs <;> omega
  omega

/-- The sum of `s_∞ = D.jetSize` over the lengths of the first `n_j = D.n j` rows, at all infinite
places `τ`, of the Young diagrams of the weight of the lift from `X_j` to `X_{j+1}`. The diagram at
`τ` has `D.columnCount τ h` columns of height `h`. -/
noncomputable def rowSizeSum {P : Parameters} (D : Data P) (j : ℕ) : ℝ :=
  ∑ τ : D.Φ, ∑ i ∈ range (D.n j),
    D.jetSize (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i))

/-- The main term `m (#Φ_a s_∞(a) + k ∑ τ, s_∞(κ(τ)))` of the size of the chain of `m` lifts, where
`s_∞ = D.jetSize`, `κ = D.weight`, `k` is the rank of the source and `Φ_a = D.aPlaces` is the set of
`a`-places, the places at which the diagrams have `a` columns of height `1`. -/
noncomputable def chainSize {P : Parameters} (D : Data P) : ℝ :=
  D.m * (#D.aPlaces * D.jetSize D.a + D.k * ∑ τ : D.Φ, D.jetSize (D.weight τ))

/-- **One kernel.** Let `j < m`, let `X_j` be the definite hermitian space over `E = D.E` with basis
`D.X j`, and let `Gf` denote the finite adelic points of its unitary group. The theta kernel
`D.liftKernel TameChar.one j` of the lift from `X_j` to `X_{j+1}`, for the trivial twisting
character, acts through the Weil representation `ω` on Schwartz functions. Apply `ω (g, g')` to the
translate `D.translateDatum t j` by `t` of the normalised vacuum function; `jetMap` turns the result
into a linear map between the Weyl modules with column numbers `D.columnCount`, whose coordinates
are indexed by `WeylIndex`. For `σ ∈ Aut ℂ`, this map multiplies the norm √`weylNormSq` of
`σ`-conjugates by at most `exp (x ^ 50 + rowSizeSum j / 2)`. Here `x = D.x` is the scale and
`rowSizeSum j` is the sum of `D.jetSize` over the row lengths of the weight. -/
lemma sqrt_weylNormSq_jetMap_le {P : Parameters} (D : Data P) (σ : ℂ ≃+* ℂ) (t : D.Translations)
    {j : ℕ} (hj : j < D.m) (g : Gf D.E (D.X j)) (g' : Gf D.E (D.X (j + 1)))
    (ξ : WeylIndex (D.X j) D.columnCount → ℂ) :
    √(weylNormSq (σ ∘ (D.liftKernel TameChar.one j).jetMap
        ((D.liftKernel TameChar.one j).ω (g, g') (D.translateDatum t j)) ξ)) ≤
      exp (D.x ^ 50 + D.rowSizeSum j / 2) * √(weylNormSq (σ ∘ ξ)) := by
  -- Apply the bound for the jets of one translate of the vacuum with growth rate `a + 1`. Its
  -- terms other than `rowSizeSum j` add up to at most `x ^ 50`, as each row has length `≤ 2 a`.
  let const : ℝ := P.constantBound * (P.q₀ * towerDeg D.towerExp * (D.n (j + 1) * D.n j) + 1) ^ 2
  let count : ℝ :=
    Fintype.card (P.Φ D.towerExp) * (D.n (j + 1) * D.n j) * log (2 * ((D.a : ℝ) + 1) + 2)
  let lengths : ℝ := ∑ τ : D.Φ, ∑ i ∈ range (D.n j),
    (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i) : ℝ) / (D.a + 1)
  have h_other : const + count + lengths / 2 ≤ D.x ^ 50 := by
    -- The instance bounds the index `j` for `le_of_hasLogBound`.
    have h_upper : D.HasLogUpper (j : ℕ) (D.logX / 2 + 2) := D.hasLogUpper_of_le hj.le
    simp only [const, count, lengths]
    grw [D.diagramWeight_le_rowMainLength_add_rowSlack hj, D.rowMainLength_add_rowSlack_le]
    simp only [n, sum_const, card_univ, card_range, nsmul_eq_mul]
    push_cast
    exact D.le_of_hasLogBound
  have h_kernel : √(weylNormSq (σ ∘ (D.liftKernel TameChar.one j).jetMap
      ((D.liftKernel TameChar.one j).ω (g, g') (D.translateDatum t j)) ξ)) ≤
      exp (const + (count + (lengths + D.rowSizeSum j) / 2)) * √(weylNormSq (σ ∘ ξ)) := by
    refine (P.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination
      (P.isVacuumCombination_finHeisenbergOp (D.homX j) (t j)) g g' D.a.succPNat
      (D.isLiftWeight_columnCount j) ξ).trans_eq ?_
    -- The conjugate of `piMBar` that scales the jets has squared norm `M`, and `#X_j = n_j`.
    rw [norm_map_star_piMBar_sq, Parameters.jetSizeBound, schurGrowthExponent,
      Fintype.card_prod (P.Φ D.towerExp), Fintype.card_prod, card_X, card_X]
    simp [const, count, lengths, rowSizeSum, jetSize, add_assoc, sum_add_distrib]
  grw [h_kernel, show const + (count + (lengths + D.rowSizeSum j) / 2) ≤
    D.x ^ 50 + D.rowSizeSum j / 2 by linarith]

/-! ### The rows -/

lemma jetSize_zero {P : Parameters} (D : Data P) : D.jetSize 0 = 0 := by simp [jetSize]

/-- Sum, over the `n_j = D.n j` rows of the Young diagram of lift `j` at the infinite place `τ`, the
size `s_∞ = D.jetSize` of the main length of the row plus `25 log b` times its slack. The main
lengths are `D.columnCount τ 1` for the first row, the weight `κ(τ) = D.weight τ` for the next
`k - 1` rows, with `k = D.k` the rank of the source, and `0` otherwise. The slacks add up to
`b + offWeight + n_j halfGap ^ 2`, where `b = D.natB` and `offWeight` are the two values of `κ` and
`halfGap = D.r ^ 8`. -/
lemma sum_range_jetSize_add_eq {P : Parameters} (D : Data P) (τ : D.Φ) (j : ℕ) :
    ∑ i ∈ range (D.n j), (D.jetSize (D.rowMainLength τ i) + 25 * D.logB * D.rowSlack i) =
      D.jetSize (D.columnCount τ 1) + (D.k - 1) * D.jetSize (D.weight τ) +
        25 * D.logB * (D.natB + D.offWeight + D.n j * D.halfGap ^ 2) := by
  have h_main : ∑ i ∈ range (D.n j), D.jetSize (D.rowMainLength τ i) =
      D.jetSize (D.columnCount τ 1) + (D.k - 1) * D.jetSize (D.weight τ) := by
    -- Split off the row `0`, then the rows `0 < i < k`; the other rows have `s_∞(0) = 0`.
    simp [rowMainLength, apply_ite D.jetSize, D.jetSize_zero, sum_ite, filter_eq', filter_ne',
      ← Nat.Ico_zero_eq_range, n]
  have h_slack :
      ∑ i ∈ range (D.n j), D.rowSlack i = D.natB + D.offWeight + D.n j * D.halfGap ^ 2 := by
    simp [rowSlack, sum_add_distrib, n]
  rw [sum_add_distrib, ← mul_sum, ← Nat.cast_sum, h_main, h_slack]
  norm_cast

/-- The chain has `m = D.m` lifts, and `rowSizeSum j` adds the sizes `s_∞ = D.jetSize` of the row
lengths of the Young diagrams of the weight of lift `j`. The sum over `j < m` is at most
`chainSize = m (#Φ_a s_∞(a) + k ∑ τ, s_∞(κ(τ)))` plus half of `errorUnit = f a log³ b`. Here
`Φ_a = D.aPlaces`, `k = D.k` is the rank of the source, `κ(τ) = D.weight τ` is the weight at the
infinite place `τ`, `f` is the number of infinite places, and `a = x b` for the scales `x`, `b`. -/
lemma sum_rowSizeSum_le {P : Parameters} (D : Data P) :
    ∑ j ∈ range D.m, D.rowSizeSum j ≤ D.chainSize + D.errorUnit / 2 := by
  -- Compare each row with its main length; each box of the slack costs at most `25 log b`.
  have h_log : 0 < D.logB := HasLogBound.pos D
  have h_box : log ((2 * D.a : ℕ) + 1) + log (D.M / P.bigOmega D.towerExp) ≤ 25 * D.logB := by
    grw [show ((2 * D.a : ℕ) + 1 : ℝ) ≤ D.b ^ 2 from D.le_of_hasLogBound,
      D.log_M_div_bigOmega_mem_Icc.2, log_pow, log_exp]
    exact le_of_eq (by ring)
  have h_row (j : ℕ) (hj : j < D.m) (τ : D.Φ) (i : ℕ) :
      D.jetSize (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i)) ≤
        D.jetSize (D.rowMainLength τ i) + 25 * D.logB * D.rowSlack i := by
    grw [D.jetSize_le_add (D.diagramWeight_le_rowMainLength_add_rowSlack hj τ i),
      D.rowMainLength_add_rowSlack_le τ i, h_box]
  have h_first : ∑ τ : D.Φ, D.jetSize (D.columnCount τ 1) = #D.aPlaces * D.jetSize D.a := by
    simp [columnCount, apply_ite D.jetSize, D.jetSize_zero]
  let main : ℝ :=
    ∑ τ : D.Φ, D.jetSize (D.columnCount τ 1) + (D.k - 1) * ∑ τ : D.Φ, D.jetSize (D.weight τ)
  let slack : ℝ := D.f * (25 * D.logB * (D.natB + D.offWeight + D.n D.m * D.halfGap ^ 2))
  have h_lift (j : ℕ) (hj : j ∈ range D.m) : D.rowSizeSum j ≤ main + slack := by
    calc D.rowSizeSum j
      _ ≤ ∑ τ : D.Φ, ∑ i ∈ range (D.n j),
          (D.jetSize (D.rowMainLength τ i) + 25 * D.logB * D.rowSlack i) := by
        grw [rowSizeSum, h_row j (mem_range.mp hj)]
      _ ≤ main + slack := by
        simp only [D.sum_range_jetSize_add_eq]
        grw [D.n_mono (mem_range.mp hj).le]
        simp [main, slack, sum_add_distrib, mul_sum]
  -- A lift has `k - 1` further rows with main length `κ(τ)`; as `s_∞ ≥ 0`, we may count `k`.
  have h_nonneg : 0 ≤ ∑ τ : D.Φ, D.jetSize (D.weight τ) := by
    refine sum_nonneg fun τ _ ↦ ?_
    calc (0 : ℝ) ≤ 20 * D.weight τ * D.logB := by positivity
      _ ≤ D.jetSize (D.weight τ) := (D.jetSize_mem_Icc D.nat_le_of_hasLogBound).1
  -- The error is `O(b log b)` for each of the `m f` pairs `(j, τ)`, and `m b ≤ a`.
  have h_error : D.m * slack ≤ D.errorUnit / 2 := D.le_of_hasLogBound
  calc ∑ j ∈ range D.m, D.rowSizeSum j
      ≤ D.m * (main + slack) := by grw [sum_le_sum h_lift, sum_const, card_range, nsmul_eq_mul]
    _ ≤ D.chainSize + D.errorUnit / 2 := by
        grw [mul_add, h_error]
        simp only [main]
        grw [h_first, sub_le_self (D.k : ℝ) zero_le_one, chainSize]

/-- The main term `chainSize = m (#Φ_a s_∞(a) + k ∑ τ, s_∞(κ(τ)))` of the size of the chain of `m`
lifts, less the saving `#Φ_a a log N` from the restriction, is at most
`h_main - m rem + 2 ∑ gain_p log p + 32 f a log b`. Here `s_∞ = D.jetSize`, `κ = D.weight`,
`Φ_a = D.aPlaces` is a subset of the `f` infinite places, the level `N` is a prime, and `a = x b`
for the scales `x`, `b`. With `s_fin = D.primeSum`, the main amount is
`h_main = m k ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))` and the total remainder is
`rem = ∑_{τ ∈ Φ_a} (s_fin(a, τ) - D.mainPrimeSum)`. -/
lemma chainSize_sub_le {P : Parameters} (D : Data P) :
    D.chainSize - #D.aPlaces * D.a * log D.N ≤
      D.mainAmount - D.m * D.totalRemainder + 2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p +
        32 * (D.f * D.a * D.logB) := by
  rw [mainAmount_sub_add_two_mul_sum_gain, chainSize]
  linarith [D.card_aPlaces_mul_excess_le]

/-! ### The terms and the restriction -/

/-- Let `X_j`, `Y_m` be the hermitian spaces over the CM field `E = D.E` of the chain of `m = D.m`
theta lifts; `Gf` denotes finite adelic points of their unitary groups and `D.FormX j` the forms on
`X_j`. Let `Ψ` be a weak chain datum for the trivial twist: coefficients of translates of the vacuum
function whose sum is invariant, with `∑ t, |σ (Ψ t)| ≤ exp (D.x ^ 60)` among the conditions.
`restrictedChain TameChar.one Ψ φ` lifts the form `φ` from `X_0` to `X_m` with these translates,
combines the results by `Ψ` and restricts to `Y_m`. If the values of `σ φ` have squared norm at most
`exp B`, then those of the `σ`-conjugate of the lift have squared norm at most `exp (B + β)`, where
`β = h_main - m rem + 2 ∑ gain_p log p + f a log³ b`. Here `h_main = D.mainAmount` is a difference
of archimedean sizes and prime sums, and `rem = D.totalRemainder` one of prime sums and their
expected mean `D.mainPrimeSum`, `gain_p` is the divisibility asked at a prime `p < D.x₁` that does
not split in `ℚ(√-d)`, `f` is the number of infinite places of `E`, and `a = x b` for the scales
`x`, `b`. -/
lemma weylNormSq_restrictedChain_le {P : Parameters} {D : Data P} {Ψ : D.Translations →₀ ℂ}
    (hΨ : D.IsWeakChainDatum 1 Ψ) {σ : ℂ ≃+* ℂ} {φ : D.SourceForm} {B : ℝ}
    (hB : ∀ g : Gf D.E (D.X 0), weylNormSq (σ ∘ (φ : D.FormX 0).val g) ≤ exp B)
    (y : Gf D.E (D.Y D.m)) :
    weylNormSq (σ ∘ (restrictedChain TameChar.one Ψ φ).val y) ≤
      exp (B + (D.mainAmount - D.m * D.totalRemainder +
        2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p + D.errorUnit)) := by
  -- A value of the chain is a sum, over tuples of classes and over `t`, of `Ψ t` times products
  -- of `m` kernels. Bound each product by `R`, count the terms, and restrict to `Y_m`.
  let size (j : ℕ) (ξ : WeylIndex (D.X j) D.columnCount → ℂ) : ℝ := √(weylNormSq (σ ∘ ξ))
  let R : ℝ := (∏ j ∈ range D.m, exp (D.x ^ 50 + D.rowSizeSum j / 2)) * √(exp B)
  let ψ : D.FormX D.m := chainCombination (1 : D.Twist).toTameChar Ψ D.translateDatum D.m φ
  let g : ∀ j : ℕ, Gf D.E (D.X j) := Pi.mulSingle D.m (D.borderU y)
  have hg : g D.m = D.borderU y := Pi.mulSingle_eq_same ..
  have h_term (t : D.Translations) (p : ∀ j : ℕ, Gf D.E (D.X j)) :
      size D.m (kernelProduct (D.liftKernel (1 : D.Twist).toTameChar) (D.translateDatum t)
        φ.val p D.m) ≤ R :=
    apply_kernelProduct_le_prod_mul _ (fun j _ ↦ size j) (fun _ ↦ exp_nonneg _)
      (fun _ ↦ D.sqrt_weylNormSq_jetMap_le σ t) (fun g ↦ sqrt_le_sqrt (hB g)) p
  have h_coeff : ∑ t ∈ Ψ.support, ‖σ (Ψ t)‖ ≤ exp (D.x ^ 60) := hΨ.sum_norm_le rfl σ
  have h_count : (Fintype.card (∀ j : Fin D.m, StdClasses (D.levelX j)) : ℝ) ≤
      exp (D.x ^ 30) ^ D.m := by
    have h_classes (j : Fin D.m) :
        (Fintype.card (StdClasses (D.levelX j)) : ℝ) ≤ exp (D.x ^ 30) := by
      rw [← Nat.card_eq_fintype_card]
      exact D.card_stdClasses_le_exp (principalLevel_le_levelX ..)
        (by grw [card_X, D.n_mono j.isLt.le])
    grw [Fintype.card_pi, Nat.cast_prod, h_classes, prod_const, card_univ, Fintype.card_fin]
  -- The value of the chain at `diag (y, 1)` is a sum over classes and translations.
  have h_chain :
      size D.m (ψ.val (D.borderU y)) ≤ exp (D.x ^ 30) ^ D.m * (exp (D.x ^ 60) * R) := by
    unfold size at h_term ⊢
    rw [← hg, chainCombination_eq_sum hΨ.isJointlyInvariant]
    calc
      _ ≤ ∑ c : ∀ j : Fin D.m, StdClasses (D.levelX j), ∑ t ∈ Ψ.support, ‖σ (Ψ t)‖ *
          √(weylNormSq (σ ∘ kernelProduct (D.liftKernel (1 : D.Twist).toTameChar)
            (D.translateDatum t) φ.val (classPoints c g) D.m)) := by
        grw [sqrt_weylNormSq_sum_le, sqrt_weylNormSq_sum_le]
        simp
      _ ≤ exp (D.x ^ 30) ^ D.m * (exp (D.x ^ 60) * R) := by
        grw [h_term]
        simp only [← sum_mul, sum_const, card_univ, nsmul_eq_mul]
        grw [h_count, h_coeff, mul_assoc]
  have h_rest : exp (70 * D.logX) + D.f * (D.m * D.halfGap) * log D.N +
      2 * (D.m * exp (30 * D.logX) + exp (60 * D.logX) + D.m * exp (50 * D.logX)) +
      32 * (D.f * D.a * D.logB) ≤ D.errorUnit / 2 :=
    D.le_of_hasLogBound
  have hx (k : ℕ) : D.x ^ k = exp (k * D.logX) := (exp_nat_mul _ _).symm
  calc weylNormSq (σ ∘ (restrictedChain TameChar.one Ψ φ).val y)
    _ ≤ exp (D.x ^ 70 - (∑ τ : D.Φ, D.branchExponent τ : ℝ) * log D.N) *
        size D.m (ψ.val (D.borderU y)) ^ 2 := by
      rw [sq_sqrt (weylNormSq_nonneg _)]
      exact D.weylNormSq_restrictToY_le σ ψ y
    _ ≤ exp (D.x ^ 70 - (#D.aPlaces * D.a - D.f * (D.m * D.halfGap)) * log D.N) *
        (exp (D.x ^ 30) ^ D.m * (exp (D.x ^ 60) * R)) ^ 2 := by
      grw [sum_branchExponent, h_chain]
    _ = exp (D.x ^ 70 - (#D.aPlaces * D.a - D.f * (D.m * D.halfGap)) * log D.N +
        2 * (D.m * D.x ^ 30 + (D.x ^ 60 +
          (D.m * D.x ^ 50 + (∑ j ∈ range D.m, D.rowSizeSum j) / 2 + B / 2)))) := by
      simp [R, ← exp_nat_mul, ← exp_sum, sum_add_distrib, ← sum_div, ← exp_half, ← exp_add]
    _ ≤ exp (B + (D.mainAmount - D.m * D.totalRemainder +
        2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p + D.errorUnit)) := by
      refine exp_le_exp.2 ?_
      simp only [hx]
      push_cast
      linarith [D.sum_rowSizeSum_le, D.chainSize_sub_le]

/-- **Size of the composite lift.** Let `Ψ` be a chain datum for the trivial twist and `σ` an
automorphism of `ℂ`. `compositeLift TameChar.one Ψ φ` lifts the form `φ` from the hermitian space
`X_0` over `E = D.E` to `X_m` by `m = D.m` theta lifts, with the glued tensor as Schwartz data, and
restricts to `Y_m`; `Gf` denotes finite adelic points. If the values of `σ φ` have squared norm at
most `exp B`, then those of the `σ`-conjugate of the lift have squared norm at most `exp (B + β)`,
where `β = h_main - m rem + 2 ∑ gain_p log p + f a log³ b`. Here `h_main = D.mainAmount` is a
difference of archimedean sizes and prime sums, and `rem = D.totalRemainder` one of prime sums and
their expected mean `D.mainPrimeSum`, `gain_p` is the divisibility asked at a prime `p < D.x₁` that
does not split in `ℚ(√-d)`, `f` is the number of infinite places of `E`, and `a = x b` for the
scales `x`, `b`. -/
theorem weylNormSq_compositeLift_le {P : Parameters} {D : Data P}
    {Ψ : D.Translations →₀ ℂ} (hΨ : D.IsChainDatum 1 Ψ) {σ : ℂ ≃+* ℂ} {φ : D.SourceForm} {B : ℝ}
    (hB : ∀ g : Gf D.E (D.X 0), weylNormSq (σ ∘ (φ : D.FormX 0).val g) ≤ exp B)
    (y : Gf D.E (D.Y D.m)) :
    weylNormSq (σ ∘ (compositeLift TameChar.one Ψ φ).val y) ≤
      exp (B + (D.mainAmount - D.m * D.totalRemainder +
        2 * ∑ p ∈ D.smallNonsplitPrimes, D.gain p * log p + D.errorUnit)) := by
  obtain ⟨Ψ', h_weak, h_eq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, D.IsWeakChainDatum 1 Ψ' ∧
      ∀ φ : D.SourceForm, compositeLift TameChar.one Ψ φ = restrictedChain TameChar.one Ψ' φ :=
    hΨ.exists_isWeakChainDatum_compositeLift_eq
  rw [h_eq φ]
  exact weylNormSq_restrictedChain_le h_weak hB y

end New.Data

end SizeBound

/-!
## Passage to target forms by the good projection

A form `z` of principal level on `Y₀` is replaced by the target form `|𝖦| e₀ s z`, its good part
(`New.Data.goodProjTranslate s z`, for `s ∈ 𝖦`).

Here `𝖦 = New.Data.chosenGL` is a finite product of groups `GL_r` over residue fields, `New.Data.e₀`
is an element of its group algebra, and `New.Data.lowerChain`, `New.Data.lowerChainAtLevel` are the
same lift with two target types.
-/

namespace New.Data

open Finset Real LevelPlaces.LevelForm

attribute [local instance low] Fintype.ofFinite

lemma coe_lowerChainAtLevel_apply {P : Parameters} {D : Data P} (ϑ : D.TameChar)
    (z : ↥(D.principalForms (D.spaceY 0))) :
    ((lowerChainAtLevel ϑ z).val : AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m)) =
      lowerChain ϑ z := rfl

/-- Let `𝖦 = D.chosenGL` be the finite group `∏ GL_r(𝔽_w)` over the chosen places `w` above `p₀`,
`p₁`, let `e₀ = D.e₀` be the good idempotent in `ℂ[𝖦]`, and let `ι = lowerChain ϑ` be the composite
of the `m` lifts from `Y₀` to `Y_m` for the tame character `ϑ`. For `s ∈ 𝖦` and a form `z` of
principal level on `Y₀`, the value at `g` of `ι (|𝖦| e₀ s z)` is the sum over `t ∈ 𝖦` of `|𝖦| e₀(t)`
times the value of `ι z` at `g * firstBlockLift ϑ (t * s)`. -/
lemma lowerChain_goodProjTranslate_apply {P : Parameters} {D : Data P} (ϑ : D.TameChar)
    (s : D.chosenGL) (z : ↥(D.principalForms (D.spaceY 0))) (g : Gf D.E (D.Y D.m)) :
    (lowerChain ϑ (D.goodProjTranslate s z).val).val g =
      ∑ t : D.chosenGL, (Nat.card D.chosenGL * D.e₀.coeff t) • (lowerChain ϑ z).val
        (g * firstBlockLift ϑ (t * s)) := by
  -- Expand the action of `e₀` as a sum over `𝖦`; the lift turns the action of `t * s` into right
  -- translation by `firstBlockLift ϑ (t * s)` (`lowerChain_principalRep`).
  simp [asAlgebraHom_eq_sum, ← Module.End.mul_apply, ← map_mul, lowerChain_principalRep, smul_sum,
    mul_smul]

/-- Passage to the good part keeps integrality. Let `j : ℂ → ℂ_l` be a ring homomorphism; a form is
integral at `j` if each value `φ(g)`, mapped by `j` and moved by `g⁻¹`, has coordinates of `l`-adic
absolute value at most `1`. Let `ι = lowerChainAtLevel ϑ` be the composite of the `m` lifts from
`Y₀` to `Y_m` for the tame character `ϑ`, with values in the forms of given level and character.
Let `𝖦 = D.chosenGL` be a finite product of groups `GL_r` over residue fields and `e₀ = D.e₀` the
central idempotent of `ℂ[𝖦]` that cuts out the good part. For `c ∈ ℂ`, `s ∈ 𝖦` and `z` of principal
level on `Y₀`, if `c • ι z` is integral at `j`, so is `c • ι (|𝖦| e₀ s z)`. -/
lemma goodProjTranslate_mem_integralForms {P : Parameters} {D : Data P} {l : ℕ} [Fact l.Prime]
    (j : PadicPlace l) {ϑ : D.TameChar} {c : ℂ} {z : ↥(D.principalForms (D.spaceY 0))}
    (h_integral : c • lowerChainAtLevel ϑ z ∈ integralForms j) (s : D.chosenGL) :
    c • lowerChainAtLevel ϑ (D.goodProjTranslate s z).val ∈ integralForms j := by
  -- The value at `g` is a sum of values of `c • lowerChainAtLevel ϑ z` at integral right translates
  -- of `g`, with algebraic integers as coefficients; the gauge is ultrametric.
  intro g
  have h_value : (c • lowerChainAtLevel ϑ (D.goodProjTranslate s z).val).val.val g =
      ∑ t : D.chosenGL, (Nat.card D.chosenGL * D.e₀.coeff t) •
        c • (lowerChain ϑ z).val (g * firstBlockLift ϑ (t * s)) := by
    change c • (lowerChainAtLevel ϑ (D.goodProjTranslate s z).val).val.val g = _
    simp only [coe_lowerChainAtLevel_apply, lowerChain_goodProjTranslate_apply, smul_sum,
      smul_comm c]
  rw [h_value]
  refine weylGauge_sum_le _ zero_le_one fun t _ ↦ ?_
  have h_int : IsIntegral ℤ (Nat.card D.chosenGL * D.e₀.coeff t) :=
    D.isCentralProj_e₀.isChar_card_mul_coeff.isIntegral _
  rw [weylGauge_smul, ← weylGauge_mul_of_mem_integralAbove
    (hk := stdLevel_le_localLevel (firstBlockLift ϑ (t * s)).2)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_isIntegral _ h_int)).trans
    (h_integral _)

/-- Size of the good part, for the trivial twist, `σ ∈ Aut ℂ` and `s ∈ 𝖦`. The map `lowerChain` is
the composite of the `m` lifts from forms of principal level on `Y₀` to algebraic forms on `Y_m`. If
every value of `lowerChain TameChar.one z`, conjugated by `σ`, has squared norm at most `exp B`,
then the lift `φ` of `D.goodProjTranslate s z`, that is of `|𝖦| e₀ s z`, has
`normSqAt φ σ ≤ exp (x ^ 99 + B)`. Here `x = D.x` is the scale, `𝖦 = D.chosenGL` is a finite product
of groups `GL_r` over residue fields and `e₀ = D.e₀` is the central idempotent of `ℂ[𝖦]` that cuts
out the good part. -/
lemma normSqAt_goodProjTranslate_le {P : Parameters} {D : Data P} {σ : ℂ ≃+* ℂ}
    {z : ↥(D.principalForms (D.spaceY 0))} {s : D.chosenGL} {B : ℝ}
    (hB : ∀ g : Gf D.E (D.Y D.m), weylNormSq (σ ∘ (D.lowerChain TameChar.one z).val g) ≤ exp B) :
    (D.lowerChainAtLevel TameChar.one (D.goodProjTranslate s z).val).normSqAt σ ≤
      exp (D.x ^ 99 + B) := by
  classical
  -- The coefficients of the central idempotent `σ e₀` have norm at most `1`, since `|𝖦| σ e₀` is
  -- the character of a representation of dimension at most `|𝖦|`.
  have h_coeff (t : D.chosenGL) : ‖σ (D.e₀.coeff t)‖ ≤ 1 := by
    simpa using (D.isCentralProj_e₀.map σ).norm_coeff_le_one t
  -- So each value is a sum of `|𝖦|` terms, each of norm at most `|𝖦| * √(exp B)`.
  have h_value (g : Gf D.E (D.Y D.m)) :
      √(weylNormSq (σ ∘ D.lowerChainAtLevel TameChar.one (D.goodProjTranslate s z).val g)) ≤
        Nat.card D.chosenGL * (Nat.card D.chosenGL * √(exp B)) := by
    let v (t : D.chosenGL) : WeylIndex (D.Y D.m) D.columnsY → ℂ :=
      (lowerChain TameChar.one z).val (g * firstBlockLift TameChar.one (t * s))
    have h_term (t : D.chosenGL) : √(weylNormSq (σ ∘ ((Nat.card D.chosenGL * D.e₀.coeff t) • v t)))
        ≤ Nat.card D.chosenGL * √(exp B) := by
      calc _ = Nat.card D.chosenGL * ‖σ (D.e₀.coeff t)‖ * √(weylNormSq (σ ∘ v t)) := by
            simp [-Fintype.card_pi, sqrt_sq_eq_abs]
        _ ≤ Nat.card D.chosenGL * √(exp B) := by grw [hB, h_coeff, mul_one]
    rw [coe_lowerChainAtLevel_apply, lowerChain_goodProjTranslate_apply]
    grw [sqrt_weylNormSq_sum_le, sum_le_sum fun t _ ↦ h_term t]
    simp [← Nat.card_eq_fintype_card]
  -- The level contains the principal level `D.piM * D.piN`, so there are at most `exp (x ^ 30)`
  -- classes.
  have h_mem (i) : D.piM * D.piN ∈ ((D.levelPlaces TameChar.one).placeAt i).asIdeal := by
    obtain ⟨i, v, h_above, hv⟩ | ⟨v, hv⟩ := i
    exacts [Ideal.mul_mem_right _ _ h_above, nomatch hv]
  grw [normSqAt, classSum_le_card_mul_sq h_value,
    D.card_stdClasses_le_exp (principalLevel_le_levelOf h_mem) (D.card_Y_le le_rfl)]
  suffices exp (D.x ^ 30) * Nat.card D.chosenGL ^ 4 ≤ exp (D.x ^ 99) by
    simpa [exp_add, ← Nat.card_eq_fintype_card, field, exp_nonneg]
  -- The order of `𝖦` divides `D.chosenGroupOrder`, and
  -- `x ^ 30 + 4 * log D.chosenGroupOrder < x ^ 99`.
  grw [Nat.le_of_dvd Fin.pos' (D.card_GL_dvd_chosenGroupOrder D.nat_le_of_hasLogBound),
    le_exp_log D.chosenGroupOrder]
  exact D.le_of_hasLogBound D.lt_of_hasLogBound

end New.Data
