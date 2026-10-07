import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
import OAI.Combinatorics.Progressions.Sampling.StagedForecastResidualBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardPrefixLog
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardBranch A stageCountConstant j x

noncomputable def preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardCap A stageCountConstant j x

noncomputable def preparedFiniteForwardModelPrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog +
    preparedFiniteForwardWork A stageCountConstant n x + stageLog + 6

noncomputable def preparedFiniteForwardSourcePrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
    2 * preparedFiniteForwardWork A stageCountConstant n x + 1

theorem preparedFiniteForwardParameter_prefix
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant n x = x +
      preparedFiniteForwardCumulative A stageCountConstant n x +
      preparedFiniteForwardPrefixLog A stageCountConstant n x + n := by
  induction n with
  | zero => simp [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      preparedFiniteForwardParameter_zero]
  | succ n ih =>
    rw [preparedFiniteForwardParameter_succ, ih]
    simp only [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem preparedFiniteForward_prefix_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) ∧
    preparedFiniteForwardPrefixLog A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) := by
  have hc : 0 ≤ preparedFiniteForwardCumulative A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardCap_nonneg A stageCountConstant j hx)
  have hb : 0 ≤ preparedFiniteForwardPrefixLog A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardBranch_nonneg A stageCountConstant j hx)
  have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  exact ⟨⟨hc, by linarith only [heq, hb, hx, hn]⟩,
    ⟨hb, by linarith only [heq, hc, hx, hn]⟩⟩

theorem preparedFiniteForward_model_precision_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
    let sourceU := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog
    0 ≤ u ∧ 0 ≤ sourceU ∧ sourceU = u + 2 * w + 1 ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog + w + stageLog + 6 ≤ u ∧
      sourceU + w ≤ 4 * b + 4 * w + 16 := by
  intro b w u sourceU
  have hp := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hbase : x ≤ b := by
    have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    change x ≤ preparedFiniteForwardParameter A stageCountConstant n x
    linarith only [heq, hp.1.1, hp.2.1, hn]
  have hu : 0 ≤ u := by
    dsimp only [u, preparedFiniteForwardModelPrecision]
    linarith only [hp.2.1, hg.1, hw, hstage.1]
  have hs : sourceU = u + 2 * w + 1 := rfl
  refine ⟨hu, by linarith only [hs, hu, hw], hs, le_rfl, ?_⟩
  have hueq : u = preparedFiniteForwardPrefixLog A stageCountConstant n x +
      gainLog + w + stageLog + 6 := rfl
  have hb : 0 ≤ b := hx.trans hbase
  have hg' : gainLog ≤ b := hg.2.trans hbase
  have ht' : stageLog ≤ b := hstage.2.trans hbase
  linarith only [hs, hueq, hp.2.2, hg', ht', hb]

theorem preparedFiniteForward_phase_cap
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n Cphase : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphase : Cphase ≤ A) :
    (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase) ^ Cphase ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  have hp := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hb := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ Cphase := Nat.cast_nonneg _
  rw [preparedFiniteForwardCap_eq]
  apply (pow_le_pow_left₀ (by linarith only [hp.2.1, hw, hC])
    (show preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase ≤
      4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A by
      have hC' : (Cphase : ℝ) ≤ A := Nat.cast_le.mpr hphase
      linarith only [hp.2.2.2.2, hC']) Cphase).trans
  exact pow_le_pow_right₀ (by linarith only [hb, hw, hA]) hphase

theorem preparedFiniteForward_branch_count_log
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x d : ℝ}
    (hx : 0 ≤ x) (hd : d ≤ x) :
    d * preparedFiniteForwardCap A stageCountConstant n x +
      (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
      (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
        stageCountConstant n ≤ preparedFiniteForwardBranch A stageCountConstant n x := by
  rw [preparedFiniteForwardBranch_eq]
  have h := mul_le_mul_of_nonneg_right hd
    (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)
  linarith only [h]

theorem preparedFiniteForward_model_scalar_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    0 ≤ w ∧ b ≤ w ∧ (count : ℝ) ≤ Real.exp w ∧ b * count ≤ w := by
  intro b w
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
  have hshift : b ≤ b + A := le_add_of_nonneg_right (Nat.cast_nonneg A)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith only [hb, hAreal]
  have hbw : b ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    have hAone : 1 ≤ A := by omega
    have hpower : b + A ≤ (b + A) ^ A := by
      simpa only [pow_one] using (pow_le_pow_right₀ hbase hAone)
    exact hshift.trans hpower
  have hsquare : b ^ 2 ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    exact (pow_le_pow_left₀ hb hshift 2).trans (pow_le_pow_right₀ hbase hA)
  refine ⟨hw, hbw, ?_, ?_⟩
  · have hc : (count : ℝ) ≤ w := hcount.trans (hxb.trans hbw)
    have he := Real.add_one_le_exp w
    linarith only [hc, he]
  · exact (mul_le_mul_of_nonneg_left (hcount.trans hxb) hb).trans
      (by simpa only [pow_two] using hsquare)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedFiniteForwardCumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) (x : ℝ) :
    preparedFiniteForwardCumulative A stageCountConstant (r + 1) x =
      preparedFiniteForwardCumulative A stageCountConstant r x +
        preparedFiniteForwardCap A stageCountConstant r x := by
  simp only [preparedFiniteForwardCumulative, Finset.sum_range_succ]

theorem preparedFiniteForwardCumulative_nonneg
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForward_prefix_bounds A stageCountConstant r hx).1.1

theorem preparedFiniteForwardCumulative_le_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCumulative_monotone
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun r => preparedFiniteForwardCumulative A stageCountConstant r x) := by
  apply monotone_nat_of_le_succ
  intro r
  exact preparedFiniteForwardCumulative_le_succ A stageCountConstant r hx

theorem preparedFiniteForwardCap_le_cumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_left (preparedFiniteForwardCumulative_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCap_le_cumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {j r : ℕ} (hjr : j < r) :
    preparedFiniteForwardCap A stageCountConstant j x ≤
      preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForwardCap_le_cumulative_succ A stageCountConstant j hx).trans
    (preparedFiniteForwardCumulative_monotone A stageCountConstant hx hjr)

theorem allocatedCandidateForwardStage_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∀ r, 0 ≤ preparedFiniteForwardCumulative A stageCountConstant r x) ∧
    (∀ r, preparedFiniteForwardCumulative A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x) ∧
    (∀ r, preparedFiniteForwardCap A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x) ∧
    (∀ r j, j < r → preparedFiniteForwardCap A stageCountConstant j x ≤
      preparedFiniteForwardCumulative A stageCountConstant r x) := by
  exact ⟨fun r => preparedFiniteForwardCumulative_nonneg A stageCountConstant r hx,
    fun r => preparedFiniteForwardCumulative_le_succ A stageCountConstant r hx,
    fun r => preparedFiniteForwardCap_le_cumulative_succ A stageCountConstant r hx,
    fun _ _ hjr => preparedFiniteForwardCap_le_cumulative A stageCountConstant hx hjr⟩

theorem allocatedCandidateForwardStage_phase_bounds
    (A : ℕ) (stageCountConstant Cphase : ℕ → ℕ) (depth : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphase : ∀ r < depth, Cphase r ≤ A) :
    let phase := fun r =>
      preparedFiniteForwardSourcePrecision A stageCountConstant r x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant r x
    (∀ r, 0 ≤ phase r) ∧
    (∀ r < depth, (phase r + Cphase r) ^ Cphase r ≤
      preparedFiniteForwardCap A stageCountConstant r x) := by
  intro phase
  refine ⟨?_, ?_⟩
  · intro r
    exact add_nonneg
      (preparedFiniteForward_model_precision_bounds A stageCountConstant r hx hg hstage).2.1
      (preparedFiniteForwardWork_nonneg A stageCountConstant r hx)
  · intro r hr
    exact preparedFiniteForward_phase_cap A stageCountConstant r (Cphase r) hx hg hstage
      (hphase r hr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_controlled_slice_bounds
    (A Cslice : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let pSlice := (b + Cslice) ^ Cslice
    0 ≤ pSlice ∧ pSlice ≤ w ∧ pSlice * count ≤ w := by
  intro b w pSlice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hA' : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCnat : Cslice ≤ A := (Nat.le_succ _).trans hC
  have hC' : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr hCnat
  have hbase : 1 ≤ b + A := by linarith only [hb, hA']
  have hbase0 : 0 ≤ b + A := le_trans (by norm_num) hbase
  have hslice0 : 0 ≤ pSlice := pow_nonneg (add_nonneg hb (Nat.cast_nonneg Cslice)) Cslice
  have hpow : pSlice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hC') Cslice
  have hcb : (count : ℝ) ≤ b + A := by
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    linarith only [hcount, hxb, hA0]
  have hw : w = (b + A) ^ A := preparedFiniteForwardWork_eq A stageCountConstant n x
  refine ⟨hslice0, hpow.trans ?_, ?_⟩
  · rw [hw]
    exact pow_le_pow_right₀ hbase hCnat
  · rw [hw]
    calc
      pSlice * count ≤ (b + A) ^ Cslice * (b + A) :=
        mul_le_mul hpow hcb (Nat.cast_nonneg count) (pow_nonneg hbase0 Cslice)
      _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
      _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_slice_mul_count_le_work
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A) (hx : 0 ≤ x)
    (hcount : (count : ℝ) ≤ x) :
    (preparedFiniteForwardParameter A constants n x + Cslice) ^ Cslice * count ≤
      preparedFiniteForwardWork A constants n x := by
  let b := preparedFiniteForwardParameter A constants n x
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
  have hCA : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr (by omega)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith
  have hpow : (b + Cslice) ^ Cslice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hCA) Cslice
  have hcount' : (count : ℝ) ≤ b + A :=
    (hcount.trans hxb).trans (le_add_of_nonneg_right (Nat.cast_nonneg A))
  rw [preparedFiniteForwardWork_eq]
  change (b + Cslice) ^ Cslice * count ≤ (b + A) ^ A
  calc
    _ ≤ (b + A) ^ Cslice * (b + A) :=
      mul_le_mul hpow hcount' (Nat.cast_nonneg count)
        (pow_nonneg (le_trans zero_le_one hbase) Cslice)
    _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
    _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

theorem preparedFiniteForward_endpoint_scalar_bounds
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ)
    {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hCslice : 1 ≤ Cslice) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hgain : 0 ≤ gainLog) (hstage : 0 ≤ stageLog)
    (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A constants n x
    let p := preparedFiniteForwardWork A constants n x
    let u := preparedFiniteForwardModelPrecision A constants n x gainLog stageLog
    let cost := b + 1
    let slice := (b + Cslice) ^ Cslice
    0 ≤ p ∧ 0 ≤ u ∧ 0 ≤ cost ∧ 0 ≤ slice ∧ cost ≤ slice ∧
      slice * count ≤ p ∧ (∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice) ∧
      2 * cost + 6 ≤ u := by
  intro b p u cost slice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg A constants n hx
  have hprefix : 0 ≤ preparedFiniteForwardPrefixLog A constants n x :=
    (preparedFiniteForward_prefix_bounds A constants n hx).2.1
  have hueq : u = preparedFiniteForwardPrefixLog A constants n x + gainLog +
      p + stageLog + 6 := rfl
  have hu : 0 ≤ u := by linarith
  have hCsliceReal : (1 : ℝ) ≤ Cslice := by exact_mod_cast hCslice
  have hbase : 1 ≤ b + Cslice := by linarith
  have hcost : 0 ≤ cost := by dsimp [cost]; linarith
  have hslice : 0 ≤ slice := pow_nonneg (le_trans zero_le_one hbase) _
  have hcostSlice : cost ≤ slice := by
    have hpower : b + Cslice ≤ (b + Cslice) ^ Cslice := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase hCslice
    dsimp only [cost, slice]
    linarith
  have hsliceCount : slice * count ≤ p :=
    preparedFiniteForward_slice_mul_count_le_work A Cslice constants n count hA hC hx hcount
  have hchart : ∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice := by
    intro chartCost hchartCost
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
    have hbcost : b ≤ cost := by dsimp [cost]; linarith
    exact hchartCost.trans (hxb.trans (hbcost.trans hcostSlice))
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbaseA : 1 ≤ b + A := by linarith
  have hsquare : (b + 2) ^ 2 ≤ p := by
    rw [show p = (b + A) ^ A from preparedFiniteForwardWork_eq A constants n x]
    exact (pow_le_pow_left₀ (by linarith) (by linarith : b + 2 ≤ b + A) 2).trans
      (pow_le_pow_right₀ hbaseA hA)
  have hcostWork : 2 * cost ≤ p := by
    dsimp only [cost]
    nlinarith [sq_nonneg b]
  refine ⟨hp, hu, hcost, hslice, hcostSlice, hsliceCount, hchart, ?_⟩
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedCandidateForwardControlInput (s d : ℕ) (b : ℝ) : ℝ :=
  ((s : ℝ) + 3) * ((d : ℝ) + 1) * (b + 1)

theorem allocatedCandidateForwardControlInput_bounds (s d : ℕ) {b : ℝ}
    (hb : 0 ≤ b) :
    0 ≤ allocatedCandidateForwardControlInput s d b ∧
    b ≤ allocatedCandidateForwardControlInput s d b ∧
    3 * b ≤ allocatedCandidateForwardControlInput s d b := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : 3 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd, mul_nonneg hs hd]
  have hthree : 3 * b ≤ allocatedCandidateForwardControlInput s d b := by
    calc
      3 * b ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  have hbthree : b ≤ 3 * b := by linarith only [hb]
  exact ⟨(mul_nonneg (by norm_num) hb).trans hthree, hbthree.trans hthree, hthree⟩

theorem allocatedCandidateForwardControlInput_denominator_bound
    (s d q : ℕ) {b x cumulative : ℝ}
    (hb : 0 ≤ b) (hxb : x ≤ b) (hcb : cumulative ≤ b)
    (hq : (q : ℝ) ≤ Real.exp x) :
    (q : ℝ) * Real.exp ((s : ℝ) * (d : ℝ) * cumulative) ≤
      Real.exp (allocatedCandidateForwardControlInput s d b) := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : (s : ℝ) * d + 1 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd]
  have hexponent : x + (s : ℝ) * d * cumulative ≤
      allocatedCandidateForwardControlInput s d b := by
    calc
      x + (s : ℝ) * d * cumulative ≤ b + (s : ℝ) * d * b :=
        add_le_add hxb (mul_le_mul_of_nonneg_left hcb (mul_nonneg hs hd))
      _ = ((s : ℝ) * d + 1) * b := by ring
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  calc
    (q : ℝ) * Real.exp ((s : ℝ) * d * cumulative) ≤
        Real.exp x * Real.exp ((s : ℝ) * d * cumulative) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _)
    _ = Real.exp (x + (s : ℝ) * d * cumulative) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem allocatedCandidateForwardControlInput_cost_bound
    (s d : ℕ) {b x cumulative Bbound : ℝ}
    (hxb : x ≤ b) (hcb : cumulative ≤ b) (hd : (d : ℝ) ≤ x)
    (hBbound : Bbound ≤ Real.exp x) :
    (d : ℝ) * Bbound * Real.exp cumulative ≤
      Real.exp (allocatedCandidateForwardControlInput s d b + 2) := by
  have hx : 0 ≤ x := (Nat.cast_nonneg d).trans hd
  have hb : 0 ≤ b := hx.trans hxb
  have hdexp : (d : ℝ) ≤ Real.exp x :=
    hd.trans (by linarith only [Real.add_one_le_exp x])
  have hthree := (allocatedCandidateForwardControlInput_bounds s d hb).2.2
  calc
    (d : ℝ) * Bbound * Real.exp cumulative ≤
        (d : ℝ) * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBbound (Nat.cast_nonneg d)) (Real.exp_nonneg _)
    _ ≤ Real.exp x * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdexp (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (x + x + cumulative) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (allocatedCandidateForwardControlInput s d b + 2) :=
      Real.exp_le_exp.mpr (by linarith only [hxb, hcb, hthree])

theorem allocatedCandidateForwardControlInput_power_bound
    (s d C A : ℕ) {b : ℝ} (hb : 0 ≤ b) (hd : (d : ℝ) ≤ b)
    (hA : 2 ≤ A) (hsA : s + 3 ≤ A) (hCA : 4 * C ≤ A) :
    (allocatedCandidateForwardControlInput s d b + C) ^ C ≤ (b + A) ^ A := by
  let K : ℝ := b + A
  have hKtwo : 2 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hb, hAreal]
  have hK : 0 ≤ K := by linarith only [hKtwo]
  have hsK : (s : ℝ) + 3 ≤ K := by
    have hsreal : (s : ℝ) + 3 ≤ A := by exact_mod_cast hsA
    dsimp only [K]
    linarith only [hb, hsreal]
  have hdK : (d : ℝ) + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hd, hAreal]
  have hbK : b + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hAreal]
  have hinput : allocatedCandidateForwardControlInput s d b ≤ K ^ 3 := by
    unfold allocatedCandidateForwardControlInput
    calc
      _ ≤ (K * K) * K :=
        mul_le_mul (mul_le_mul hsK hdK (by positivity) hK) hbK (by positivity)
          (mul_nonneg hK hK)
      _ = K ^ 3 := by ring
  have hCK : (C : ℝ) ≤ K := by
    have hCnat : C ≤ A := by omega
    have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hCnat
    dsimp only [K]
    linarith only [hb, hCreal]
  have hKcube : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hKtwo] : 1 ≤ K)
      (by norm_num : (1 : ℕ) ≤ 3)
  have hbase : allocatedCandidateForwardControlInput s d b + C ≤ K ^ 4 := by
    calc
      _ ≤ K ^ 3 + K ^ 3 := add_le_add hinput (hCK.trans hKcube)
      _ = 2 * K ^ 3 := by ring
      _ ≤ K * K ^ 3 := mul_le_mul_of_nonneg_right hKtwo (pow_nonneg hK _)
      _ = K ^ 4 := by ring
  calc
    _ ≤ (K ^ 4) ^ C := pow_le_pow_left₀
      (add_nonneg (allocatedCandidateForwardControlInput_bounds s d hb).1 (Nat.cast_nonneg C)) hbase C
    _ = K ^ (4 * C) := (pow_mul _ _ _).symm
    _ ≤ K ^ A := pow_le_pow_right₀ (by linarith only [hKtwo]) hCA
    _ = (b + A) ^ A := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem le_preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (depth : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hA : 1 ≤ A) (hdepth : 0 < depth) :
    x ≤ preparedFiniteForwardCumulative A stageCountConstant depth x := by
  have hcap : x ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    rw [preparedFiniteForwardCap_eq, preparedFiniteForwardParameter_zero]
    have hw := preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx
    have hbase : 1 ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    have hshift : x ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    exact hshift.trans (by simpa only [pow_one] using pow_le_pow_right₀ hbase hA)
  exact hcap.trans (preparedFiniteForwardCap_le_cumulative A stageCountConstant hx hdepth)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardParameter_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardParameter A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)

theorem le_preparedFiniteForwardCount
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  (le_preparedFiniteForwardParameter A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_le_count A stageCountConstant n hx)

theorem preparedFiniteForwardCap_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_left (preparedFiniteForwardParameter_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardCumulative_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x :=
  (preparedFiniteForward_prefix_bounds A stageCountConstant n hx).1.2.trans
    (preparedFiniteForwardParameter_le_count A stageCountConstant n hx)

theorem preparedFiniteForwardCount_le_parameter_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant (n + 1) x := by
  rw [preparedFiniteForwardCount_eq, preparedFiniteForwardParameter_succ]
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith only [hbranch]

theorem preparedFiniteForwardCount_le_parameter
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {n depth : ℕ} (hn : n < depth) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant depth x :=
  (preparedFiniteForwardCount_le_parameter_succ A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_monotone A stageCountConstant hx hn)

theorem preparedFiniteForwardTreeStorage_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (depth : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    let Bphase := preparedFiniteForwardCumulative A stageCountConstant depth x
    let pTree := preparedFiniteForwardParameter A stageCountConstant depth x
    0 ≤ pTree ∧ Bphase ≤ pTree ∧
      ∀ n : ℕ, n < depth →
        preparedFiniteForwardCap A stageCountConstant n x ≤ Bphase ∧
        preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 pTree ∧
        preparedFiniteForwardCumulative A stageCountConstant n x ≤
          preparedFiniteForwardCount A stageCountConstant n x ∧
        preparedFiniteForwardCap A stageCountConstant n x ≤
          preparedFiniteForwardCount A stageCountConstant n x ∧
        x ≤ preparedFiniteForwardCount A stageCountConstant n x := by
  refine ⟨preparedFiniteForwardParameter_nonneg A stageCountConstant depth hx,
    (preparedFiniteForward_prefix_bounds A stageCountConstant depth hx).1.2, ?_⟩
  intro n hn
  exact ⟨preparedFiniteForwardCap_le_cumulative A stageCountConstant hx hn,
    ⟨preparedFiniteForwardCount_nonneg A stageCountConstant n hx,
      preparedFiniteForwardCount_le_parameter A stageCountConstant hx hn⟩,
    preparedFiniteForwardCumulative_le_count A stageCountConstant n hx,
    preparedFiniteForwardCap_le_count A stageCountConstant n hx,
    le_preparedFiniteForwardCount A stageCountConstant n hx⟩

theorem preparedFiniteForwardTreeStorage_structural_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (depth dim blocksPerStage : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (hdim : (dim : ℝ) ≤ x)
    (hblocks : ((depth * blocksPerStage : ℕ) : ℝ) ≤ x) :
    (dim : ℝ) ≤ preparedFiniteForwardParameter A stageCountConstant depth x ∧
      ((depth * blocksPerStage : ℕ) : ℝ) ≤
        preparedFiniteForwardParameter A stageCountConstant depth x ∧
      ∀ n : ℕ, n < depth →
        (dim : ℝ) ≤ preparedFiniteForwardCount A stageCountConstant n x ∧
        (((n + 1) * blocksPerStage : ℕ) : ℝ) ≤
          preparedFiniteForwardCount A stageCountConstant n x := by
  have hstored := le_preparedFiniteForwardParameter A stageCountConstant depth hx
  refine ⟨hdim.trans hstored, hblocks.trans hstored, ?_⟩
  intro n hn
  have hlocal := le_preparedFiniteForwardCount A stageCountConstant n hx
  refine ⟨hdim.trans hlocal, ?_⟩
  exact (Nat.cast_le.mpr (Nat.mul_le_mul_right blocksPerStage hn)).trans
    (hblocks.trans hlocal)

end Erdos3.VectorPolynomial

end

end OAI
