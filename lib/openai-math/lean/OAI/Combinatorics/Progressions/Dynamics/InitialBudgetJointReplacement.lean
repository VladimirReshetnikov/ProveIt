import OAI.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
import OAI.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff

namespace OAI

section

namespace Erdos3

noncomputable def replacementCutoffInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  6 * physicalReplacementInputLog m n P + P + 3 * d + 10

noncomputable def replacementCommonInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  4 * replacementCutoffInputLog m n d P + 2 * P + 10

theorem replacementCutoffInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCutoffInputLog m n d P ∧
    P ≤ replacementCutoffInputLog m n d P ∧
    6 * physicalReplacementInputLog m n P + 6 ≤ replacementCutoffInputLog m n d P ∧
    3 * (d : ℝ) + 2 ≤ replacementCutoffInputLog m n d P ∧
    2 * (d : ℝ) ≤ replacementCutoffInputLog m n d P := by
  have hW := physicalReplacementInputLog_nonneg m n hP
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  unfold replacementCutoffInputLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem replacementCommonInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCommonInputLog m n d P ∧
    P ≤ replacementCommonInputLog m n d P ∧
    replacementCutoffInputLog m n d P ≤ replacementCommonInputLog m n d P ∧
    4 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    3 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    2 * P + 3 ≤ replacementCommonInputLog m n d P := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  unfold replacementCommonInputLog
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith
  constructor <;> linarith [hb.1]

theorem replacement_binary_power_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (2 * d) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  apply (pow_le_pow_left₀ (by norm_num) h2 d).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem replacement_ternary_power_le_exp (d : ℕ) : 2 * (3 : ℝ) ^ d ≤ Real.exp (3 * d + 2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ Real.exp 2 * (Real.exp 3) ^ d := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem replacementCutoffInputLog_power_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (2 : ℝ) ^ (d - 1) ≤ Real.exp (replacementCutoffInputLog m n d P) ∧
    2 * (3 : ℝ) ^ d ≤ Real.exp (replacementCutoffInputLog m n d P) := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  constructor
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le d 1)).trans
    exact (replacement_binary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.2)
  · exact (replacement_ternary_power_le_exp d).trans (Real.exp_le_exp.mpr hb.2.2.2.1)

theorem parameter_min_of_log_scale {c P R L M : ℝ} (hc : 0 < c)
    (hcinv : c⁻¹ ≤ Real.exp P) (hL : Real.exp (R + P) ≤ L) (hrelative : c * L ≤ M) :
    Real.exp R ≤ M := by
  have hdiv : Real.exp R / c ≤ L := by
    calc
      _ = Real.exp R * c⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp R * Real.exp P := mul_le_mul_of_nonneg_left hcinv (Real.exp_nonneg _)
      _ = Real.exp (R + P) := (Real.exp_add _ _).symm
      _ ≤ L := hL
  have h := (div_le_iff₀ hc).mp hdiv
  exact h.trans (by simpa only [mul_comm] using hrelative)

end Erdos3

end

section

namespace Erdos3

theorem replacement_selected_parameter_bounds (m n d D : ℕ) {K A Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hCwidth : Cwidth ≤ Real.exp P) (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Z := replacementCommonInputLog m n d P
    0 < tol ∧ tol⁻¹ ≤ Real.exp Z ∧
    0 < integerBoxRetainedGap d D c tol ∧ (integerBoxRetainedGap d D c tol)⁻¹ ≤ Real.exp Z ∧
    ((D * integerBoxGcdCutoff d Cwidth tol : ℕ) : ℝ) ≤ Real.exp Z ∧
    integerBoxPairScale d Cwidth tol ≤ Real.exp Z := by
  intro tol Z
  let T := replacementCutoffInputLog m n d P
  have hb := replacementCutoffInputLog_bounds m n d hP
  have hz := replacementCommonInputLog_bounds m n d hP
  have hpows := replacementCutoffInputLog_power_bounds m n d hP
  have ht : 0 < tol := weightedReplacementTolerance_pos (by positivity) heps0
  have hti : tol⁻¹ ≤ Real.exp T :=
    (physicalReplacementTolerance_inverse_le_exp m n hK0 hA0 heps0 hP hK hA heps).trans
      (Real.exp_le_exp.mpr hb.2.2.1)
  have hexp : Real.exp P ≤ Real.exp T := Real.exp_le_exp.mpr hb.2.1
  have hq := integerBoxGcdModulus_le_exp d D hCwidth0 ht hb.1 hpows.1
    (hDlog.trans hexp) (hCwidth.trans hexp) hti
  have hk := integerBoxRetainedGap_inverse_le_exp d D hD hc0 ht hb.1 hpows.2 (hc.trans hexp) hti
  have hs := integerBoxPairScale_le_exp d hCwidth0 ht hb.1 hpows.1 hpows.2 (hCwidth.trans hexp) hti
  refine ⟨ht, hti.trans (Real.exp_le_exp.mpr hz.2.2.1), ?_, ?_, ?_, ?_⟩
  · unfold integerBoxRetainedGap
    exact mul_pos (mul_pos (by exact_mod_cast hD) (integerBoxNearRatio_spec d ht).1) hc0
  · exact hk.trans (Real.exp_le_exp.mpr (by linarith [hz.2.2.2.2.1]))
  · exact hq.trans (Real.exp_le_exp.mpr hz.2.2.2.1)
  · exact hs.trans (Real.exp_le_exp.mpr hz.2.2.2.2.1)

theorem replacement_common_geometric_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) {C A P : ℝ} (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (n : ℝ) ≤ Real.exp Z ∧ (Fintype.card J : ℝ) ≤ Real.exp Z ∧
    C ≤ Real.exp Z ∧ A ≤ Real.exp Z ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp Z ∧
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp Z ∧
    (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp Z := by
  intro Z
  have hz := replacementCommonInputLog_bounds m n (Fintype.card J) hP
  have ht := replacementCutoffInputLog_bounds m n (Fintype.card J) hP
  have hexp : Real.exp P ≤ Real.exp Z := Real.exp_le_exp.mpr hz.2.1
  refine ⟨hn.trans hexp, hcard.trans hexp, hC.trans hexp, hA.trans hexp, hprofile.trans hexp, ?_, ?_⟩
  · exact (smoothPairRowLipschitz_le_exp k hP hcard hprofile).trans (Real.exp_le_exp.mpr hz.2.2.2.2.2)
  · apply (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Fintype.card_subtype_le (fun j : J => j ≠ k))).trans
    apply (replacement_binary_power_le_exp (Fintype.card J)).trans
    exact Real.exp_le_exp.mpr (ht.2.2.2.2.trans hz.2.2.1)

theorem selectedPhysicalReplacementThreshold_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n degree : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    physicalReplacementScaleThreshold n k Q C κ A tol degree Z Z ≤
      Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k}) degree Z + 16) := by
  intro tol Q κ Z
  obtain ⟨ht, hti, hk, hki, hq, _⟩ := replacement_selected_parameter_bounds m n (Fintype.card J) D
    hP hK0 hA0 hCwidth0 hc0 heps0 hD hDlog hK hA hCwidth hc heps
  obtain ⟨hn', hcard', hC', hA', hprofile', hrow', hpow'⟩ :=
    replacement_common_geometric_bounds m n k hP hn hcard hC hA hprofile
  exact physicalReplacementScaleThreshold_le_exp n degree k Q
    (replacementCommonInputLog_bounds m n (Fintype.card J) hP).1 hC0 hk hA0 ht
    hn' hq hC' hki hA' hti hcard' hrow' hpow' hprofile'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem initial_budget_weighted_physical_replacement {J I : Type*}
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
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hdim0 : (Fintype.card I : ℝ) ≤ Real.exp P0)
    (hparamLog : (Fintype.card J : ℝ) ≤ Real.exp P0)
    (hDlog : (D : ℝ) ≤ Real.exp P0) (hKlog : K ≤ Real.exp P0)
    (hAlog : A ≤ Real.exp P0) (hClog : C ≤ Real.exp P0)
    (hWidthlog : Cwidth ≤ Real.exp P0) (hcinv : c⁻¹ ≤ Real.exp P0)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
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
    let Z := replacementCommonInputLog (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) P0
    ∀ (hLlog : Real.exp (Z + P0) ≤ L) (hdegree : 2 * Z ≤ (degree : ℝ))
      (hsizeExp : ∀ i, Real.exp (2 * physicalReplacementThresholdLog (Fintype.card I)
        (Fintype.card {j : J // j ≠ k0}) degree Z + 16) * L ^ exponent ≤ H i),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let hsize := fun i => (mul_le_mul_of_nonneg_right
      (selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile)
      (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree Z Z
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤ epsilon := by
  intro F E tol B Q κ Z hLlog hdegree hsizeExp W hW
  have hz := replacementCommonInputLog_bounds (Fintype.card (Option J × I)) (Fintype.card I)
    (Fintype.card J) hP0
  obtain ⟨_, _, _, _, hq, hs⟩ := replacement_selected_parameter_bounds
    (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) D
    hP0 hK hA hCwidth hc heps hD hDlog hKlog hAlog hWidthlog hcinv hepsinv
  have hparScale := hs.trans (parameter_min_of_log_scale hc hcinv hLlog hrelative)
  have hQdegree := nat_le_two_pow_of_le_exp hq hdegree
  have hdim : (Fintype.card I : ℝ) ≤ Real.exp Z :=
    hdim0.trans (Real.exp_le_exp.mpr hz.2.1)
  have hT := selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile
  have hsize (i : I) := (mul_le_mul_of_nonneg_right hT
    (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
  exact small_weighted_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA heps hK hc hCwidth hD
    hleft hright origin lo N degree exponent hexponent f hf Z Z hz.1 hdim hupper hratio R parMin hparMin
    hparamDim hparSide hparWidth hwidthRatio hrelative winLo winHi hwin hwinScale v hv
    hparScale hq hsize hQdegree hW

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem initial_budget_joint_physical_replacement {J I : Type*}
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
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hdim0 : (Fintype.card I : ℝ) ≤ Real.exp P0)
    (hparamLog : (Fintype.card J : ℝ) ≤ Real.exp P0)
    (hDlog : (D : ℝ) ≤ Real.exp P0) (hKlog : K ≤ Real.exp P0)
    (hAlog : A ≤ Real.exp P0) (hClog : C ≤ Real.exp P0)
    (hWidthlog : Cwidth ≤ Real.exp P0) (hcinv : c⁻¹ ≤ Real.exp P0)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (R : ℕ) (parMin : ℝ) (hparMin : 0 < parMin) (hparamDim : 2 ≤ Fintype.card J)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hwidthRatio : (R : ℝ) ≤ Cwidth * parMin) (hrelative : c * L ≤ parMin)
    (winLo winHi : Option J × I → ℤ) (hwin : ∀ i, winLo i < winHi i)
    (hwinScale : ∀ i, smoothPairCoefficientScale (H i.2) L i.1 ≤
      K * ((winHi i - winLo i : ℤ) : ℝ))
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z : (∀ i, Finset.Ico (winLo i) (winHi i)),
      0 ≤ v (fun i => (z i).val) ∧ v (fun i => (z i).val) ≤ 1) :
    let F := (3 * K) ^ Fintype.card (Option J × I)
    let E := (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I
    let tol := weightedReplacementTolerance F E epsilon
    let B := integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let Q := D * B
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) P0
    ∀ (hLlog : Real.exp (Z + P0) ≤ L) (hdegree : 2 * Z ≤ (degree : ℝ))
      (hsizeExp : ∀ i, Real.exp (2 * physicalReplacementThresholdLog (Fintype.card I)
        (Fintype.card {j : J // j ≠ k0}) degree Z + 16) * L ^ exponent ≤ H i),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let hsize := fun i => (mul_le_mul_of_nonneg_right
      (selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile)
      (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree Z Z
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |((integerBoxUniformWeights parLo parHi hpar).prod
      (integerBoxUniformWeights winLo winHi hwin)).mean
        (fun tz => v (fun i => (tz.2 i).val) *
          physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
            (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val)
              (fun i => (tz.2 i).val)))| ≤ epsilon := by
  intro F E tol B Q κ Z hLlog hdegree hsizeExp W hW hsize rho sc hlarge hwhole P hpos
  apply integerBox_joint_error_of_window_tests winLo winHi hwin parLo parHi hpar
    (fun z t => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z)) epsilon ?_ v hv
  intro v' hv'
  exact initial_budget_weighted_physical_replacement k0 D anchor parLo parHi hpar H
    hL hC hA heps hK hc hCwidth hD hleft hright origin lo N degree exponent hexponent f hf
    P0 hP0 hdim0 hparamLog hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile
    hupper hratio R parMin hparMin hparamDim hparSide hparWidth hwidthRatio hrelative
    winLo winHi hwin hwinScale v' hv' hLlog hdegree hsizeExp hW

end Erdos3

end

end OAI
