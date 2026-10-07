import OAI.Combinatorics.Progressions.Dynamics.PreparedLateScalarPowerBudget
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface

namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedSourceScalarData where
  D : ℝ
  pRadius : ℝ
  Ptail : ℝ
  Prho : ℝ
  Pk : ℝ
  target : ℝ
  F : ℝ
  Tmod : ℝ
  Ppert : ℝ
  Epert : ℝ
  Bstruct : ℝ
  Pmin : ℝ
  Elog : ℝ
  Vlog : ℝ
  master : ℝ
  Pphysical : ℝ
  lateTarget : ℝ
  Eforecast : ℝ
  gainLog : ℝ

namespace PreparedSourceScalarData

def values (v : PreparedSourceScalarData) : List ℝ :=
  [v.D, v.pRadius, v.Ptail, v.Prho, v.Pk, v.target, v.F, v.Tmod, v.Ppert, v.Epert, v.Bstruct, v.Pmin, v.Elog, v.Vlog, v.master, v.Pphysical, v.lateTarget, v.Eforecast, v.gainLog]

def Bounded (v : PreparedSourceScalarData) (P : ℝ) : Prop :=
  ∀ x ∈ v.values, x ∈ Set.Icc 0 P

theorem Bounded.mono {v : PreparedSourceScalarData} {P Q : ℝ}
    (hv : v.Bounded P) (hPQ : P ≤ Q) : v.Bounded Q :=
  fun x hx => ⟨(hv x hx).1, (hv x hx).2.trans hPQ⟩

noncomputable def scale (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  v.pRadius + v.Ptail + fixedPathPerturbationLog v.D (v.D + v.Ppert + 4) v.Epert m

noncomputable def seed (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  allocatedScaleLog (v.D + v.scale m +
    allocatedAffineLengthLog m v.D (v.scale m) v.Prho v.Pk v.target v.F v.Tmod + 1)

def witnessWidth (v : PreparedSourceScalarData) : ℝ :=
  2 * v.Bstruct + 2 * v.Vlog + 5 * v.Elog + 24

noncomputable def certificateBase (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  1 + (v.Bstruct + v.scale m + v.pRadius) + v.seed m + v.witnessWidth +
    v.Pmin + v.Elog + v.Vlog

noncomputable def lateMaster (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  preparedModularGeneralDetectorLateMaster v.master (v.seed m) v.witnessWidth
    v.Pphysical v.lateTarget + (1 + (v.seed m) ^ 2) * v.Pmin + v.scale m

noncomputable def required (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  let width := 4 * (v.lateMaster m + 8) ^ 2
  preparedForecastProductiveRequired m v.master (v.lateMaster m) v.Eforecast
    (preparedForecastGoodCertificateBudget (v.certificateBase m) v.Bstruct width v.gainLog v.Vlog)
    (preparedForecastGoodAnalyticBudget (preparedCenteredForecastSpatialExponent m)
      (v.certificateBase m) v.Bstruct width v.gainLog v.Vlog) width

end PreparedSourceScalarData

theorem exists_preparedCompleteSourceRank_power_budget (m inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ v : PreparedSourceScalarData, v.Bounded ((p + 2) ^ inputPower) →
      v.required m ≤ (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (v.required m) ≤ (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤ Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  obtain ⟨seedPower, _, hseed⟩ := exists_preparedPerturbativeSeed_power_budget m inputPower
  let firstPower := max inputPower seedPower
  obtain ⟨latePower, _, hlate⟩ := exists_preparedLateScalar_power_budget firstPower
  let fullPower := max firstPower latePower
  obtain ⟨requiredPower, hrequiredPower, hrequired⟩ :=
    exists_preparedForecastConstructedRequired_power_budget m fullPower
  refine ⟨requiredPower, hrequiredPower, ?_⟩
  intro p hp v hv
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hfirst : (p + 2) ^ inputPower ≤ (p + 2) ^ firstPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have hseedFirst : (p + 2) ^ seedPower ≤ (p + 2) ^ firstPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  have hfull : (p + 2) ^ firstPower ≤ (p + 2) ^ fullPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have hlateFull : (p + 2) ^ latePower ≤ (p + 2) ^ fullPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  have hvFirst := hv.mono hfirst
  have hvFull := hvFirst.mono hfull
  have hcap (x : ℝ) (hx : x ∈ v.values) := hv x hx
  have hcapFirst (x : ℝ) (hx : x ∈ v.values) := hvFirst x hx
  have hcapFull (x : ℝ) (hx : x ∈ v.values) := hvFull x hx
  obtain ⟨_, hscale, hseedBound⟩ := hseed hp0 v.D v.pRadius v.Ptail v.Prho v.Pk
    v.target v.F v.Tmod v.Ppert v.Epert
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
  change v.scale m ∈ Set.Icc 0 ((p + 2) ^ seedPower) at hscale
  change v.seed m ∈ Set.Icc 0 ((p + 2) ^ seedPower) at hseedBound
  obtain ⟨_, hcert, hLateBound, hMasterLate⟩ := hlate hp0 v.Bstruct (v.scale m) v.pRadius
    (v.seed m) v.Pmin v.Elog v.Vlog v.master v.Pphysical v.lateTarget
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    ⟨hscale.1, hscale.2.trans hseedFirst⟩
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    ⟨hseedBound.1, hseedBound.2.trans hseedFirst⟩
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
  change v.certificateBase m ∈ Set.Icc 0 ((p + 2) ^ latePower) at hcert
  change v.lateMaster m ∈ Set.Icc 0 ((p + 2) ^ latePower) at hLateBound
  have hbound : v.required m ≤ (p + 2) ^ requiredPower :=
    hrequired p hp v.master (v.lateMaster m) v.Eforecast (v.certificateBase m)
      v.Bstruct v.gainLog v.Vlog
      (hcapFull _ (by simp [PreparedSourceScalarData.values])).1 hMasterLate
      (hLateBound.2.trans hlateFull)
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      ⟨hcert.1, hcert.2.trans hlateFull⟩
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound,
    preparedRoundedRank_le_exp hp requiredPower⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def PreparedSourceScalarData.shortRequired (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  let width := 4 * (v.lateMaster m + 8) ^ 2
  preparedShortForecastProductiveRequired m v.master (v.lateMaster m) v.Eforecast
    (preparedForecastGoodCertificateBudget (v.certificateBase m) v.Bstruct width v.gainLog v.Vlog)
    (preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
      (v.certificateBase m) v.Bstruct width v.gainLog v.Vlog) width

theorem exists_preparedCompleteShortSourceRank_power_budget (m inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ v : PreparedSourceScalarData, v.Bounded ((p + 2) ^ inputPower) →
      v.shortRequired m ≤ (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (v.shortRequired m) ≤ (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤ Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  obtain ⟨seedPower, _, hseed⟩ := exists_preparedPerturbativeSeed_power_budget m inputPower
  let firstPower := max inputPower seedPower
  obtain ⟨latePower, _, hlate⟩ := exists_preparedLateScalar_power_budget firstPower
  let fullPower := max firstPower latePower
  obtain ⟨requiredPower, hrequiredPower, hrequired⟩ :=
    exists_preparedShortForecastConstructedRequired_power_budget m fullPower
  refine ⟨requiredPower, hrequiredPower, ?_⟩
  intro p hp v hv
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hfirst : (p + 2) ^ inputPower ≤ (p + 2) ^ firstPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have hseedFirst : (p + 2) ^ seedPower ≤ (p + 2) ^ firstPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  have hfull : (p + 2) ^ firstPower ≤ (p + 2) ^ fullPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have hlateFull : (p + 2) ^ latePower ≤ (p + 2) ^ fullPower :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  have hvFirst := hv.mono hfirst
  have hvFull := hvFirst.mono hfull
  have hcap (x : ℝ) (hx : x ∈ v.values) := hv x hx
  have hcapFirst (x : ℝ) (hx : x ∈ v.values) := hvFirst x hx
  have hcapFull (x : ℝ) (hx : x ∈ v.values) := hvFull x hx
  obtain ⟨_, hscale, hseedBound⟩ := hseed hp0 v.D v.pRadius v.Ptail v.Prho v.Pk
    v.target v.F v.Tmod v.Ppert v.Epert
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
    (hcap _ (by simp [PreparedSourceScalarData.values]))
  change v.scale m ∈ Set.Icc 0 ((p + 2) ^ seedPower) at hscale
  change v.seed m ∈ Set.Icc 0 ((p + 2) ^ seedPower) at hseedBound
  obtain ⟨_, hcert, hLateBound, hMasterLate⟩ := hlate hp0 v.Bstruct (v.scale m) v.pRadius
    (v.seed m) v.Pmin v.Elog v.Vlog v.master v.Pphysical v.lateTarget
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    ⟨hscale.1, hscale.2.trans hseedFirst⟩
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    ⟨hseedBound.1, hseedBound.2.trans hseedFirst⟩
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
    (hcapFirst _ (by simp [PreparedSourceScalarData.values]))
  change v.certificateBase m ∈ Set.Icc 0 ((p + 2) ^ latePower) at hcert
  change v.lateMaster m ∈ Set.Icc 0 ((p + 2) ^ latePower) at hLateBound
  have hbound : v.shortRequired m ≤ (p + 2) ^ requiredPower :=
    hrequired p hp v.master (v.lateMaster m) v.Eforecast (v.certificateBase m)
      v.Bstruct v.gainLog v.Vlog
      (hcapFull _ (by simp [PreparedSourceScalarData.values])).1 hMasterLate
      (hLateBound.2.trans hlateFull)
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      ⟨hcert.1, hcert.2.trans hlateFull⟩
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
      (hcapFull _ (by simp [PreparedSourceScalarData.values]))
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound,
    preparedRoundedRank_le_exp hp requiredPower⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedUniformSourceRank_power_budget (s inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m : ℕ, m ≤ s →
      ∀ v : PreparedSourceScalarData, v.Bounded ((p + 2) ^ inputPower) →
      v.required m ≤ (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (v.required m) ≤ (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤
        Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  let exponent (m : ℕ) :=
    (exists_preparedCompleteSourceRank_power_budget m inputPower).choose
  let requiredPower := 2 + ∑ k ∈ Finset.range (s + 1), exponent k
  refine ⟨requiredPower, by dsimp [requiredPower]; omega, ?_⟩
  intro p hp m hm v hv
  have hexponent : exponent m ≤ requiredPower := by
    have hsum : exponent m ≤ ∑ k ∈ Finset.range (s + 1), exponent k :=
      Finset.single_le_sum (f := exponent) (fun k _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp only [requiredPower]
    omega
  have hlocal :=
    ((exists_preparedCompleteSourceRank_power_budget m inputPower).choose_spec.2 hp v hv).1
  change v.required m ≤ (p + 2) ^ exponent m at hlocal
  have hbound : v.required m ≤ (p + 2) ^ requiredPower :=
    hlocal.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hexponent)
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound,
    preparedRoundedRank_le_exp hp requiredPower⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedUniformShortSourceRank_power_budget (s inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m : ℕ, m ≤ s →
      ∀ v : PreparedSourceScalarData, v.Bounded ((p + 2) ^ inputPower) →
      v.shortRequired m ≤ (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (v.shortRequired m) ≤ (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤
        Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  let exponent (m : ℕ) :=
    (exists_preparedCompleteShortSourceRank_power_budget m inputPower).choose
  let requiredPower := 2 + ∑ k ∈ Finset.range (s + 1), exponent k
  refine ⟨requiredPower, by dsimp [requiredPower]; omega, ?_⟩
  intro p hp m hm v hv
  have hexponent : exponent m ≤ requiredPower := by
    have hsum : exponent m ≤ ∑ k ∈ Finset.range (s + 1), exponent k :=
      Finset.single_le_sum (f := exponent) (fun k _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp only [requiredPower]
    omega
  have hlocal :=
    ((exists_preparedCompleteShortSourceRank_power_budget m inputPower).choose_spec.2 hp v hv).1
  change v.shortRequired m ≤ (p + 2) ^ exponent m at hlocal
  have hbound : v.shortRequired m ≤ (p + 2) ^ requiredPower :=
    hlocal.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hexponent)
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound,
    preparedRoundedRank_le_exp hp requiredPower⟩

end Erdos3.VectorPolynomial

end

end OAI
