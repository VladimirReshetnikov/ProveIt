import OAI.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
import OAI.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
import OAI.Combinatorics.Progressions.Lattices.IntegerWindowFactor

namespace OAI

section

namespace Erdos3

noncomputable def weightedReplacementTolerance (F E epsilon : ℝ) : ℝ :=
  replacementAccuracy (F ^ 2 * (1 + E)) (epsilon ^ 2)

theorem weightedReplacementTolerance_pos {F E epsilon : ℝ}
    (hE : 0 ≤ E) (heps : 0 < epsilon) :
    0 < weightedReplacementTolerance F E epsilon :=
  (replacementAccuracy_spec (mul_nonneg (sq_nonneg F) (by linarith)) (sq_pos_of_pos heps)).1

theorem weightedReplacementTolerance_bound {F E epsilon beta : ℝ}
    (hF : 0 ≤ F) (hE : 0 ≤ E) (heps : 0 < epsilon) (hbeta : 0 ≤ beta)
    (hsmall : beta ≤ weightedReplacementTolerance F E epsilon) :
    F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hcost := (replacementAccuracy_spec
    (mul_nonneg (sq_nonneg F) (by linarith : 0 ≤ 1 + E)) (sq_pos_of_pos heps)).2.2
  change F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon ≤ epsilon ^ 2 at hcost
  have harg : 0 ≤ E * beta + weightedReplacementTolerance F E epsilon := by positivity
  have hsquare : (F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon)) ^ 2 ≤
      epsilon ^ 2 := by
    calc
      _ = F ^ 2 * (E * beta + weightedReplacementTolerance F E epsilon) := by
        rw [mul_pow, Real.sq_sqrt harg]
      _ ≤ F ^ 2 * (E * weightedReplacementTolerance F E epsilon +
          weightedReplacementTolerance F E epsilon) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hsmall hE) le_rfl) (sq_nonneg F)
      _ = F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon := by ring
      _ ≤ epsilon ^ 2 := hcost
  exact (sq_le_sq₀ (mul_nonneg hF (Real.sqrt_nonneg _)) heps.le).mp hsquare

theorem cutoff_weighted_replacement_bound (d R : ℕ) {F E epsilon C M : ℝ}
    (hd : 2 ≤ d) (hF : 0 ≤ F) (hE : 0 ≤ E) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C (weightedReplacementTolerance F E epsilon) ≤ M)
    (hR : (R : ℝ) ≤ C * M) :
    F * Real.sqrt (E * integerBoxBadPairBudget d
      (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon)) R
      ⌊integerBoxNearRatio d (weightedReplacementTolerance F E epsilon) * M⌋₊ M +
      weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hM : 0 ≤ M := by
    have h : (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon) : ℝ) ≤ M :=
      (le_max_left _ _).trans hscale
    exact (Nat.cast_nonneg _).trans h
  exact weightedReplacementTolerance_bound hF hE heps
    (integerBoxBadPairBudget_nonneg _ _ _ _ hM)
    (integerBoxBadPairBudget_of_cutoffs d R hd hC htol hscale hR)

end Erdos3

end

section

namespace Erdos3

theorem weightedReplacementTolerance_inverse_le_exp {F E epsilon P : ℝ}
    (hF0 : 0 ≤ F) (hE0 : 0 ≤ E) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hF : F ≤ Real.exp P) (hE : E ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance F E epsilon)⁻¹ ≤ Real.exp (6 * P + 6) := by
  have hcoef : F ^ 2 * (1 + E) ≤ Real.exp (3 * P + 2) := by
    calc
      _ ≤ (Real.exp P) ^ 2 * Real.exp (P + 1) :=
        mul_le_mul (pow_le_pow_left₀ hF0 hF 2) (one_add_le_exp_succ hP hE)
          (by linarith) (by positivity)
      _ = Real.exp (3 * P + 1) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have heps2 : (epsilon ^ 2)⁻¹ ≤ Real.exp (3 * P + 2) := by
    calc
      _ = (epsilon⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (Real.exp P) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr heps0.le) heps 2
      _ = Real.exp (2 * P) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (2 * (3 * P + 2) + 2) :=
      replacementAccuracy_inverse_le_exp (by positivity) (sq_pos_of_pos heps0)
        (by linarith) hcoef heps2
    _ = _ := by congr 1; ring

theorem replacementWindowFactor_le_exp (m : ℕ) {K P : ℝ}
    (hK0 : 0 ≤ K) (hK : K ≤ Real.exp P) :
    (3 * K) ^ m ≤ Real.exp ((m : ℝ) * (P + 3)) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 3 * K ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := mul_le_mul h3 hK hK0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 3 * K) hbase m

theorem replacementSampledEnergy_le_exp (n : ℕ) {A P : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    (2 : ℝ) ^ (n + 1) * A ^ n ≤ Real.exp ((n : ℝ) * P + 2 * (n + 1)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ (Real.exp 2) ^ (n + 1) * (Real.exp P) ^ n :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h2 _) (pow_le_pow_left₀ hA0 hA _)
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

noncomputable def physicalReplacementInputLog (m n : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) * (P + 3) + n * P + 2 * (n + 1) + P + 1

theorem physicalReplacementInputLog_nonneg (m n : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementInputLog m n P := by
  unfold physicalReplacementInputLog
  positivity

theorem physicalReplacementTolerance_inverse_le_exp (m n : ℕ) {K A epsilon P : ℝ}
    (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon)⁻¹ ≤
      Real.exp (6 * physicalReplacementInputLog m n P + 6) := by
  apply weightedReplacementTolerance_inverse_le_exp (by positivity) (by positivity) heps0
    (physicalReplacementInputLog_nonneg m n hP)
  · apply (replacementWindowFactor_le_exp m hK0 hK).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]
  · apply (replacementSampledEnergy_le_exp n hA0 hA).trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3)]
  · apply heps.trans
    apply Real.exp_le_exp.mpr
    unfold physicalReplacementInputLog
    nlinarith [mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (by linarith : 0 ≤ P + 3),
      mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hP]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_physical_residual_sum_energy {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (Q degree : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog accLog eta : ℝ) (hmodLog : 0 ≤ modLog) (heta : eta ≤ 1)
    (hacc : Real.exp (-accLog) ≤ eta) (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    (∑ x ∈ translatedIntegerBox lo N, physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f x ^ 2) ≤
      (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) * (translatedIntegerBox lo N).card := by
  let P := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  have hstep := normalizedBoxPartitions_step N H ρ hlarge hwhole
  have hN (i : I) : 0 < N i := by
    have h : (0 : ℝ) < N i := by linarith [hlarge i, hwhole i]
    exact_mod_cast h
  have hlo : lo ∈ translatedIntegerBox lo N := (mem_translatedIntegerBox lo N lo).mpr
    (fun i => ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hN i)⟩)
  let : Nonempty (translatedIntegerBox lo N) := ⟨⟨lo, hlo⟩⟩
  have hc (c : ∀ i, (P i).Label) := physicalBoxResidual_control_of_lengths lo N P hstep hpos
    (boundedPrimePower Q) (boundedPrimePower_pairwise Q) degree f hf modLog dimLog accLog eta hmodLog heta hacc
    (fun j => (Nat.cast_le.mpr (boundedPrimePower_le Q j)).trans hQlog) hdim
    (fun i c => (hlength i).trans (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).1) c
  have h := physicalBoxResidual_energy lo N P hstep hpos (boundedPrimePower Q) degree f eta hc
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort (translatedIntegerBox lo N)
      (fun x => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f x ^ 2)] at h
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨lo, hlo⟩))).mp h

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalMeanAccuracyLog {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  -Real.log (physicalPairMeanAccuracy n k Q C κ A degree epsilon)

theorem physicalMeanAccuracyLog_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ}
    (hA : 0 ≤ A) (heps : 0 < epsilon) :
    0 ≤ physicalMeanAccuracyLog n k Q C κ A degree epsilon ∧
      Real.exp (-physicalMeanAccuracyLog n k Q C κ A degree epsilon) =
        physicalPairMeanAccuracy n k Q C κ A degree epsilon := by
  have h := physicalPairMeanAccuracy_spec n k Q C κ degree hA heps
  constructor
  · have hl := Real.log_le_log h.1 h.2.1
    rw [Real.log_one] at hl
    exact neg_nonneg.mpr hl
  · simp only [physicalMeanAccuracyLog, neg_neg, Real.exp_log h.1]

noncomputable def physicalReplacementScaleThreshold {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) (degree : ℕ) (modLog dimLog : ℝ) : ℝ :=
  replacementScaleThreshold C (physicalPairPointAccuracy n k Q C κ A epsilon)
    (physicalPairGridAccuracy n k C κ A epsilon)
    (Real.exp (modLog * (2 * degree : ℕ) + physicalMeanAccuracyLog n k Q C κ A degree epsilon + dimLog + 1))
    Q 2 (8 * probabilityProfileLipschitz)

theorem physicalReplacementScaleThreshold_conditions {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) (modLog dimLog : ℝ)
    {A epsilon L H : ℝ} {N e : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : physicalReplacementScaleThreshold n k Q C κ A epsilon degree modLog dimLog * L ^ e ≤ H)
    (hupper : H ≤ 2 * (N : ℝ)) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    let accLog := physicalMeanAccuracyLog n k Q C κ A degree epsilon
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ rho * H / 4 ∧
      (Q : ℝ) ≤ N ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hd := physicalPairPointAccuracy_spec n k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec n k C κ hA heps
  exact replacementScaleThreshold_conditions hC hd.1 hr.1 (Real.exp_nonneg _) (Nat.cast_nonneg Q)
    (by norm_num) (by positivity) hL he hscale hupper (by nlinarith [hr.2.1])

theorem smoothPairCoefficientScale_large {I J : Type*} (H : I → ℝ) {L U : ℝ}
    (hL : 1 ≤ L) (hU : 0 ≤ U) (hH : ∀ i, U ≤ H i / L) :
    ∀ z : Option J × I, U ≤ smoothPairCoefficientScale (H z.2) L z.1 := by
  rintro ⟨j, i⟩
  cases j with
  | none =>
      exact (le_mul_of_one_le_right hU hL).trans ((le_div_iff₀ (zero_lt_one.trans_le hL)).mp (hH i))
  | some j => exact hH i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ)
    (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree)
    (B R : ℕ) (hBQ : D * B ≤ Q) (hB : 0 < B) (hparamDim : 2 ≤ Fintype.card J)
    (parMin : ℝ) (hparMin : 0 < parMin)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hscale : ∀ z : Option J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
      smoothPairCoefficientScale (H z.2) L z.1)
    (W : Finset (Option J × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2)
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option J × I) *
        (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card) *
      Real.sqrt (((∏ i, 2 / H i) * ((1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) *
        (translatedIntegerBox lo N).card)) * integerBoxBadPairBudget (Fintype.card J) B R r parMin +
        physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ) := by
  let P := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  let e : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
  have heta0 : 0 ≤ eta := (Real.exp_pos _).le.trans hacc
  have hepsilon := physicalResidualPairBudget_nonneg lo N H k0 Q C κ δ degree eta ρ hδ heta0 hρ
  have henergy := normalized_physical_residual_sum_energy lo N H ρ hlarge hwhole Q degree f hf
    modLog dimLog accLog eta hmodLog heta hacc hQlog hdim hlength
  have hmass := affine_parameter_bad_pair_probability parLo parHi hpar D Q B R r anchor hBQ hB hparamDim
    hparMin hparSide hparWidth
  have hgood (tu : (∀ j, Finset.Ico (parLo j) (parHi j)) × (∀ j, Finset.Ico (parLo j) (parHi j)))
      (htu : ¬ affineParameterBadPair D Q r anchor (fun j => (tu.1 j).val) (fun j => (tu.2 j).val)) :=
    retained_physical_residual_correlation k0 D r anchor parLo parHi tu.1 tu.2 H Q hH hL hC hκ hδ hδ1
      hleft hright hgap htu hmesh hsmall origin hZ lo N hside degree f f hf hf eta ρ modLog dimLog accLog
      hρ heta hmodLog hacc hQlog hdim hlarge hwhole hlength hQdegree
  have h := smooth_window_weighted_sampled_error (fun z => (origin z : ℝ))
    (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
    (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ hscale W hW
    (integerBoxUniformWeights parLo parHi hpar) (fun t j => anchor j + (D : ℤ) * (t j).val)
    (translatedIntegerBox lo N) e (physicalBoxResidual_zero_off lo N P hpos (boundedPrimePower Q) degree f)
    (by positivity : 0 ≤ 1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) hepsilon henergy
    (fun tu => affineParameterBadPair D Q r anchor (fun j => (tu.1 j).val) (fun j => (tu.2 j).val)) hmass hgood v hv
  simpa only [integerBoxUniformWeights_mean, smoothPairCoefficientScale] using h

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalMeanAccuracyLog_le (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    physicalMeanAccuracyLog n k Q C κ A degree epsilon ≤ 2 * physicalPairMeanLog n degree P + 2 := by
  have hi := physicalPairMeanAccuracy_inverse_le_exp n degree k Q hP hC0 hκ0 hA0 heps0 hQ hC hκ hA heps hpow
  have hp := (physicalPairMeanAccuracy_spec n k Q C κ degree hA0 heps0).1
  have hl := Real.log_le_log (inv_pos.mpr hp) hi
  simpa only [physicalMeanAccuracyLog, Real.log_inv, Real.log_exp] using hl

noncomputable def physicalReplacementThresholdLog (n d degree : ℕ) (P : ℝ) : ℝ :=
  2 * physicalPairCoefficientLog n d P + 2 * physicalPairMeanLog n degree P +
    (2 * degree + 2) * P + 20

theorem physicalReplacementThresholdLog_bounds (n d degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementThresholdLog n d degree P ∧
    P + 8 ≤ physicalReplacementThresholdLog n d degree P ∧
    2 * physicalPairCoefficientLog n d P + 2 ≤ physicalReplacementThresholdLog n d degree P ∧
    2 * physicalPairMeanLog n degree P + 2 + (2 * degree + 1) * P + 1 ≤
      physicalReplacementThresholdLog n d degree P := by
  have hc := (physicalPairCoefficientLog_bounds n d hP).1
  have hm := (physicalPairMeanLog_bounds n degree hP).1
  have hdegree : (0 : ℝ) ≤ degree := Nat.cast_nonneg _
  have hprod := mul_nonneg hdegree hP
  unfold physicalReplacementThresholdLog
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem physicalReplacementScaleThreshold_le_exp (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    physicalReplacementScaleThreshold n k Q C κ A epsilon degree P P ≤
      Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k}) degree P + 16) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hb := physicalReplacementThresholdLog_bounds n d degree hP
  have hPR : P ≤ physicalReplacementThresholdLog n d degree P := by linarith [hb.2.1]
  have hexp := Real.exp_le_exp.mpr hPR
  have hpointgrid := physicalPairPointGridAccuracy_inverse_le_exp n k Q hP hC0 hκ0 hA0 heps0
    hn hQ hC hκ hA heps hcard hrow hpow
  have hmean := physicalMeanAccuracyLog_le n degree k Q hP hC0 hκ0 hA0 heps0 hQ hC hκ hA heps hpow
  have hd := (physicalPairPointAccuracy_spec n k Q C κ hA0 heps0).1
  have hr := (physicalPairGridAccuracy_spec n k C κ hA0 heps0).1
  unfold physicalReplacementScaleThreshold
  apply replacementScaleThreshold_le_exp hC0 hd hr (Nat.cast_nonneg Q) hb.1
  · exact hC.trans hexp
  · exact hpointgrid.1.trans (Real.exp_le_exp.mpr hb.2.2.1)
  · exact hpointgrid.2.trans (Real.exp_le_exp.mpr hb.2.2.1)
  · apply Real.exp_le_exp.mpr
    push_cast
    have hlast := hb.2.2.2
    nlinarith
  · exact hQ.trans hexp
  · have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact h2.trans (Real.exp_le_exp.mpr (by linarith [hb.2.1]))
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 hprofile (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (P + 8) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hb.2.1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem allocated_weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C κ A epsilon : ℝ} (Q : ℕ)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog : ℝ) (hmodLog : 0 ≤ modLog)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog) (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hsize : ∀ i, physicalReplacementScaleThreshold (Fintype.card I) k0 Q C κ A epsilon degree modLog dimLog *
      L ^ exponent ≤ H i)
    (hQdegree : Q ≤ 2 ^ degree)
    (B R : ℕ) (hBQ : D * B ≤ Q) (hB : 0 < B) (hparamDim : 2 ≤ Fintype.card J)
    (parMin : ℝ) (hparMin : 0 < parMin)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (W : Finset (Option J × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2)
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A epsilon
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA heps hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option J × I) *
        (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card) *
      Real.sqrt ((2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I *
        integerBoxBadPairBudget (Fintype.card J) B R r parMin + epsilon) := by
  let delta := physicalPairPointAccuracy (Fintype.card I) k0 Q C κ A epsilon
  let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A epsilon
  let eta := physicalPairMeanAccuracy (Fintype.card I) k0 Q C κ A degree epsilon
  let accLog := physicalMeanAccuracyLog (Fintype.card I) k0 Q C κ A degree epsilon
  have sc (i : I) := physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
    (zero_le_one.trans hC) hA heps hL hexponent (hsize i) (hupper i)
  have hH (i : I) : 0 < H i := (sc i).1
  have hlarge (i : I) : 4 ≤ rho * H i := (sc i).2.2.1
  have hwhole (i : I) : rho * H i ≤ 2 * N i := (sc i).2.2.2.2.2.2
  let P := normalizedBoxPartitions N H rho hlarge hwhole
  let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
  have hd := physicalPairPointAccuracy_spec (Fintype.card I) k0 Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec (Fintype.card I) k0 C κ hA heps
  have he := physicalPairMeanAccuracy_spec (Fintype.card I) k0 Q C κ degree hA heps
  have halog := physicalMeanAccuracyLog_spec (Fintype.card I) k0 Q C κ degree hA heps
  have hscale := smoothPairCoefficientScale_large (J := J) H hL
    (show 0 ≤ 8 * (probabilityProfileLipschitz : ℝ) by positivity) (fun i => (sc i).2.2.2.2.2.1)
  have hZ := shiftedSmoothProductMass_pos_of_large_scales (fun z => (origin z : ℝ))
    (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1) hscale
  have h := weighted_physical_replacement k0 D r anchor parLo parHi hpar H Q hH hL hC hκ hd.1.le hd.2.1
    hleft hright hgap (fun i => (sc i).2.1) hd.2.2.2 origin hZ lo N (fun i => (sc i).2.2.2.2.1)
    degree f hf eta rho modLog dimLog accLog hr.1.le he.2.1 hmodLog halog.2.le hQlog hdim hlarge hwhole
    (fun i => (sc i).2.2.2.1) hQdegree B R hBQ hB hparamDim parMin hparMin hparSide hparWidth hscale W hW v hv
  have hp := physicalResidualPairBudget_of_accuracies lo N H hH k0 Q C κ degree hA heps hratio
  have heta : 0 ≤ eta := he.1.le
  have hcap0 := residueTruncationCap_nonneg (BoundedPrime Q) degree heta
  have hcap := residueTruncationCap_le_envelope (BoundedPrime Q) degree he.2.1
  have hE : 1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2 ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0 hcap 2) heta
    have henergy := he.2.2.1
    change eta * residualCapEnvelope (BoundedPrime Q) degree ^ 2 ≤ 1 at henergy
    linarith
  have hvol := translated_box_volume_ratio_le lo N H hH hratio
  have henergy : (∏ i, 2 / H i) * ((1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) *
      (translatedIntegerBox lo N).card) ≤ (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I := by
    calc
      _ = ((2 : ℝ) ^ Fintype.card I * ((translatedIntegerBox lo N).card / ∏ i, H i)) *
          (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2) := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
        ring
      _ ≤ ((2 : ℝ) ^ Fintype.card I * A ^ Fintype.card I) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hvol (by positivity)) hE (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hbad : 0 ≤ integerBoxBadPairBudget (Fintype.card J) B R r parMin := by
    unfold integerBoxBadPairBudget
    positivity
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option J × I) *
      (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg (fun z _ => (smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1).le)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hfactor
  apply Real.sqrt_le_sqrt
  exact add_le_add (mul_le_mul_of_nonneg_right henergy hbad) hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem small_weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C A epsilon K c Cwidth : ℝ}
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hK : 0 ≤ K) (hc : 0 < c) (hCwidth : 0 ≤ Cwidth) (hD : 0 < D)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog : ℝ) (hmodLog : 0 ≤ modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (R : ℕ) (parMin : ℝ) (hparMin : 0 < parMin) (hparamDim : 2 ≤ Fintype.card J)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hwidthRatio : (R : ℝ) ≤ Cwidth * parMin) (hrelative : c * L ≤ parMin)
    (winLo winHi : Option J × I → ℤ) (hwin : ∀ i, winLo i < winHi i)
    (hwinScale : ∀ i, smoothPairCoefficientScale (H i.2) L i.1 ≤
      K * ((winHi i - winLo i : ℤ) : ℝ))
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let F := (3 * K) ^ Fintype.card (Option J × I)
    let E := (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I
    let tol := weightedReplacementTolerance F E epsilon
    let B := integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let Q := D * B
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    ∀ (hparamScale : integerBoxPairScale (Fintype.card J) Cwidth tol ≤ parMin)
      (hQlog : (Q : ℝ) ≤ Real.exp modLog)
      (hsize : ∀ i, physicalReplacementScaleThreshold (Fintype.card I) k0 Q C κ A tol degree modLog dimLog *
        L ^ exponent ≤ H i)
      (hQdegree : Q ≤ 2 ^ degree),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤ epsilon := by
  intro F E tol B Q κ hparamScale hQlog hsize hQdegree W hW
  let r := ⌊integerBoxNearRatio (Fintype.card J) tol * parMin⌋₊
  have hF : 0 ≤ F := by positivity
  have hE : 0 ≤ E := by positivity
  have htol : 0 < tol := weightedReplacementTolerance_pos hE heps
  have hgap := integerBoxRetainedGap_spec (Fintype.card J) D hD hc htol hrelative
  have hB := (integerBoxGcdCutoff_spec (Fintype.card J) (C := Cwidth) htol).1
  have h := allocated_weighted_physical_replacement k0 D r anchor parLo parHi hpar H Q
    hL hC hgap.1 hA htol hleft hright hgap.2 origin lo N degree exponent hexponent f hf
    modLog dimLog hmodLog hQlog hdim hupper hratio hsize hQdegree B R le_rfl hB hparamDim
    parMin hparMin hparSide hparWidth W hW v hv
  have hH (i : I) : 0 < H i :=
    (physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA htol hL hexponent (hsize i) (hupper i)).1
  have hfactor := integerIntervalBox_window_factor_le winLo winHi hwin
    (fun i : Option J × I => smoothPairCoefficientScale (H i.2) L i.1)
    (fun i => (smoothPairCoefficientScale_pos (hH i.2) (zero_lt_one.trans_le hL) i.1).le) hwinScale
  have hfinal := cutoff_weighted_replacement_bound (Fintype.card J) R hparamDim hF hE hCwidth heps
    hparamScale hwidthRatio
  exact h.trans ((mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _)).trans hfinal)

end Erdos3

end

end OAI
