import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedFiniteForwardFrontProjectionPrecision (u p native : ℝ) : ℝ :=
  u + 2 * p + max (max native 3) (2 * u + 4 * p + 20) + 32

theorem preparedFiniteForwardFrontProjectionPrecision_nonneg
    {u p native : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    0 ≤ preparedFiniteForwardFrontProjectionPrecision u p native := by
  have hmax : 2 * u + 4 * p + 20 ≤ max (max native 3) (2 * u + 4 * p + 20) :=
    le_max_right _ _
  unfold preparedFiniteForwardFrontProjectionPrecision
  linarith only [hu, hp, hmax]

theorem exists_preparedFiniteForwardFrontProjectionPrecision_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t u p native : ℝ}, 0 ≤ t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      preparedFiniteForwardFrontProjectionPrecision u p native ∈ Set.Icc 0 ((t + C) ^ C) := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C Cnative) ^ Cnative +
    9 * Polynomial.X + 55
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro t u p native ht hu hp hn
  let v : ℝ := (t + Cnative) ^ Cnative
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hcommon : max native 3 ≤ v + 3 :=
    max_le (by linarith only [hn.2]) (by linarith only [hv])
  have hmax : max (max native 3) (2 * u + 4 * p + 20) ≤ v + 6 * t + 23 :=
    max_le (by linarith only [hcommon, ht]) (by linarith only [hu.2, hp.2, hv])
  have hbudget : v + 9 * t + 55 ≤ (t + C) ^ C := by
    simpa [Q, v, Polynomial.eval₂_pow] using hpoly t ht
  refine ⟨preparedFiniteForwardFrontProjectionPrecision_nonneg hu.1 hp.1, ?_⟩
  unfold preparedFiniteForwardFrontProjectionPrecision
  linarith only [hmax, hu.2, hp.2, hbudget]

theorem exists_preparedFiniteForwardFrontProjection_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog native : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
      let p := preparedFiniteForwardWork A stageCountConstant n x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n false
        x gainLog stageLog + p
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      preparedFiniteForwardFrontProjectionPrecision u p native ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteForwardFrontProjectionPrecision_budget Cnative
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant n x gainLog stageLog native hx hg hs u p t hn
  have hprecision := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs
  have hu : 0 ≤ u := hprecision.1
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have htEq : t = u + 3 * p + 1 := by
    dsimp only [t]
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    have heq : preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog =
        u + 2 * p + 1 := hprecision.2.2.1
    rw [heq]
    ring
  have ht : 0 ≤ t := by linarith only [htEq, hu, hp]
  exact hbound ht ⟨hu, by linarith only [htEq, hp]⟩
    ⟨hp, by linarith only [htEq, hu, hp]⟩ hn

noncomputable def preparedFiniteForwardFrontProjectionExponent (Cnative : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardFrontProjection_budget Cnative)

theorem preparedFiniteForwardFrontProjectionExponent_two_le (Cnative : ℕ) :
    2 ≤ preparedFiniteForwardFrontProjectionExponent Cnative :=
  (Classical.choose_spec (exists_preparedFiniteForwardFrontProjection_budget Cnative)).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedFiniteScheduleLocalDegreeRequired
    {Stage : Type*} [Fintype Stage] (m : ℕ) (degree : Stage → ℕ)
    (Pmaster : Stage → ℝ) (Plate E extraRequired : ℝ) : ℝ :=
  let r := fun k => preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate
  let modelRequired := fun k => max (r k).required
    ((max (r k).Pproj E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
  max (∑ k, max 0 (modelRequired k)) extraRequired

theorem exists_preparedFiniteScheduleRequiredRank_power_budget
    (m cutoff stageCount inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧
      ∀ {Stage : Type*} [Fintype Stage] (degree : Stage → ℕ),
      (∀ k, degree k ≤ cutoff) → Fintype.card Stage ≤ stageCount →
      ∀ {p : ℝ}, 2 ≤ p → ∀ (Pmaster : Stage → ℝ) (Plate E extraRequired : ℝ),
      (∀ k, 0 ≤ Pmaster k) → (∀ k, Pmaster k ≤ Plate) →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      extraRequired ≤ (p + 2) ^ inputPower →
      preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E extraRequired ≤
        (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E extraRequired) ≤
        (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤
        Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  obtain ⟨C, _, hresources⟩ := exists_preparedModularGeneral_cutoff_resource_budget m cutoff
  let A := preparedCenteredMarginalExponent m
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let B : Polynomial ℕ := (2 * U + Polynomial.C C) ^ C
  let V : Polynomial ℕ := B + (B + U + Polynomial.C A) ^ A
  let envelope : Polynomial ℕ := Polynomial.C stageCount * V + U
  obtain ⟨requiredPower, hpower, henvelope⟩ := exists_natPolynomial_fixed_power_budget envelope
  refine ⟨requiredPower, hpower, ?_⟩
  intro Stage _ degree hdegree hcard p hp Pmaster Plate E extraRequired
    hMaster hMasterLate hPlate hE hextra
  let u := (p + 2) ^ inputPower
  let b := (2 * u + C) ^ C
  let v := b + (b + u + A) ^ A
  let r := fun k => preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hmarg0 : 0 ≤ (b + u + A) ^ A := by positivity
  have hv : 0 ≤ v := add_nonneg hb hmarg0
  have hmodel (k : Stage) : max 0
      (max (r k).required ((max (r k).Pproj E + A) ^ A)) ≤ v := by
    have hres := hresources (hMaster k) (hMasterLate k) (degree k) (hdegree k)
    have hlate0 := (hMaster k).trans (hMasterLate k)
    have hresbound : (Pmaster k + Plate + C) ^ C ≤ b := by
      apply pow_le_pow_left₀
        (add_nonneg (add_nonneg (hMaster k) hlate0) (Nat.cast_nonneg C))
      change Pmaster k + Plate + C ≤ 2 * u + C
      have hmaster := (hMasterLate k).trans hPlate
      linarith only [hmaster, hPlate]
    have hrequired : (r k).required ≤ b := hres.required.2.trans hresbound
    have hproj : (r k).Pproj ≤ b := hres.Pproj.2.trans hresbound
    have hmarg : (max (r k).Pproj E + A) ^ A ≤ (b + u + A) ^ A := by
      apply pow_le_pow_left₀
        (add_nonneg (hres.Pproj.1.trans (le_max_left _ _)) (Nat.cast_nonneg A))
      apply add_le_add _ le_rfl
      exact max_le (hproj.trans (le_add_of_nonneg_right hu))
        (hE.trans (le_add_of_nonneg_left hb))
    apply max_le hv
    exact max_le (hrequired.trans (le_add_of_nonneg_right hmarg0))
      (hmarg.trans (le_add_of_nonneg_left hb))
  have hsum : (∑ k : Stage, max 0
      (max (r k).required ((max (r k).Pproj E + A) ^ A))) ≤ (stageCount : ℝ) * v := by
    calc
      _ ≤ ∑ _k : Stage, v := Finset.sum_le_sum (fun k _ => hmodel k)
      _ = (Fintype.card Stage : ℝ) * v := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hv
  have hbound : preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E extraRequired ≤ (p + 2) ^ requiredPower := by
    have htotal : (stageCount : ℝ) * v + u ≤ (p + 2) ^ requiredPower := by
      simpa [envelope, V, B, U, v, b, u, Polynomial.eval₂_pow] using
        henvelope p (by linarith : 0 ≤ p)
    apply le_trans (b := (stageCount : ℝ) * v + u) _ htotal
    change max (∑ k : Stage, max 0
      (max (r k).required ((max (r k).Pproj E + A) ^ A))) extraRequired ≤ _
    exact max_le (hsum.trans (le_add_of_nonneg_right hu))
      (hextra.trans (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hv)))
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound, preparedRoundedRank_le_exp hp requiredPower⟩

theorem exists_preparedFiniteScheduleUniformRequiredRank_power_budget
    (s cutoff stageCount inputPower : ℕ) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧
      ∀ m : ℕ, m ≤ s →
      ∀ {Stage : Type*} [Fintype Stage] (degree : Stage → ℕ),
      (∀ k, degree k ≤ cutoff) → Fintype.card Stage ≤ stageCount →
      ∀ {p : ℝ}, 2 ≤ p → ∀ (Pmaster : Stage → ℝ) (Plate E extraRequired : ℝ),
      (∀ k, 0 ≤ Pmaster k) → (∀ k, Pmaster k ≤ Plate) →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      extraRequired ≤ (p + 2) ^ inputPower →
      preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E extraRequired ≤
        (p + 2) ^ requiredPower ∧
      1 ≤ preparedRoundedRank p requiredPower ∧
      Real.exp (preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E extraRequired) ≤
        (preparedRoundedRank p requiredPower : ℝ) ∧
      (preparedRoundedRank p requiredPower : ℝ) ≤
        Real.exp ((p + 2) ^ (requiredPower + 1)) := by
  let exponent (m : ℕ) :=
    (exists_preparedFiniteScheduleRequiredRank_power_budget m cutoff stageCount inputPower).choose
  let requiredPower := 2 + ∑ j ∈ Finset.range (s + 1), exponent j
  refine ⟨requiredPower, by dsimp only [requiredPower]; omega, ?_⟩
  intro m hm Stage _ degree hdegree hcard p hp Pmaster Plate E extraRequired
    hMaster hMasterLate hPlate hE hextra
  have hexponent : exponent m ≤ requiredPower := by
    have hsum : exponent m ≤ ∑ j ∈ Finset.range (s + 1), exponent j :=
      Finset.single_le_sum (f := exponent) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp only [requiredPower]
    omega
  have hlocal := ((exists_preparedFiniteScheduleRequiredRank_power_budget
    m cutoff stageCount inputPower).choose_spec.2 degree hdegree hcard hp
      Pmaster Plate E extraRequired hMaster hMasterLate hPlate hE hextra).1
  change preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E extraRequired ≤
    (p + 2) ^ exponent m at hlocal
  have hbound : preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E extraRequired ≤ (p + 2) ^ requiredPower :=
    hlocal.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hexponent)
  exact ⟨hbound, preparedRoundedRank_one_le p requiredPower,
    preparedRoundedRank_exp_requirement hbound, preparedRoundedRank_le_exp hp requiredPower⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedConditionalExcessRequired (m : ℕ) (Plate E : ℝ) : ℝ :=
  (max (4 * (Plate + 8) ^ 2) E + allocatedExternalConditionalExcessExponent m) ^
    allocatedExternalConditionalExcessExponent m

theorem preparedConditionalExcessRequired_le_preparedFiniteScheduleLocalDegreeRequired
    {Stage : Type*} [Fintype Stage] (m : ℕ) (degree : Stage → ℕ)
    (Pmaster : Stage → ℝ) (Plate E : ℝ) :
    preparedConditionalExcessRequired m Plate E ≤
      preparedFiniteScheduleLocalDegreeRequired m degree Pmaster Plate E
        (preparedConditionalExcessRequired m Plate E) := by
  exact le_max_right _ _

theorem preparedFiniteScheduleConditionalExcess_exp_le
    {Stage : Type*} [Fintype Stage] (m : ℕ) (degree : Stage → ℕ)
    (Pmaster : Stage → ℝ) (Plate E : ℝ) {bound : ℝ}
    (hbound : Real.exp (preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E (preparedConditionalExcessRequired m Plate E)) ≤ bound) :
    Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^
        allocatedExternalConditionalExcessExponent m) ≤ bound := by
  exact (Real.exp_le_exp.mpr
    (preparedConditionalExcessRequired_le_preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E)).trans hbound

theorem preparedFiniteScheduleConditionalExcess_size_rank
    {Stage X : Type*} [Fintype Stage] (m : ℕ) (degree : Stage → ℕ)
    (Pmaster : Stage → ℝ) (Plate E : ℝ) (N : X → ℕ) (rank : ℝ)
    (hsize : ∀ x, Real.exp (preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E (preparedConditionalExcessRequired m Plate E)) ≤ (N x : ℝ))
    (hRank : Real.exp (preparedFiniteScheduleLocalDegreeRequired
      m degree Pmaster Plate E (preparedConditionalExcessRequired m Plate E)) ≤ rank) :
    (∀ x, Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^
        allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ)) ∧
    Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^
        allocatedExternalConditionalExcessExponent m) ≤ rank := by
  exact ⟨fun x => preparedFiniteScheduleConditionalExcess_exp_le
    m degree Pmaster Plate E (hsize x),
    preparedFiniteScheduleConditionalExcess_exp_le m degree Pmaster Plate E hRank⟩

theorem exists_preparedFiniteScheduleConditionalExcess_power_budget (m inputPower : ℕ) :
    ∃ extraPower : ℕ, 2 ≤ extraPower ∧
      ∀ {p Plate E : ℝ}, 2 ≤ p → 0 ≤ Plate →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ extraPower := by
  let A := allocatedExternalConditionalExcessExponent m
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let Q : Polynomial ℕ := (4 * (U + 8) ^ 2 + U + Polynomial.C A) ^ A
  obtain ⟨extraPower, hpower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨extraPower, hpower, ?_⟩
  intro p Plate E hp hPlate0 hPlate hE
  let u := (p + 2) ^ inputPower
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hproj : 4 * (Plate + 8) ^ 2 ≤ 4 * (u + 8) ^ 2 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ Plate + 8)
        (add_le_add hPlate le_rfl) 2) (by norm_num)
  have hmax : max (4 * (Plate + 8) ^ 2) E ≤ 4 * (u + 8) ^ 2 + u := by
    exact max_le (hproj.trans (le_add_of_nonneg_right hu))
      (hE.trans (le_add_of_nonneg_left (by positivity)))
  have hbound : preparedConditionalExcessRequired m Plate E ≤
      (4 * (u + 8) ^ 2 + u + A) ^ A := by
    apply pow_le_pow_left₀
      (add_nonneg ((by positivity : 0 ≤ 4 * (Plate + 8) ^ 2).trans
        (le_max_left _ _)) (Nat.cast_nonneg A))
    exact add_le_add hmax le_rfl
  apply hbound.trans
  simpa [Q, U, u, Polynomial.eval₂_pow] using hQ p (by linarith : 0 ≤ p)

theorem exists_preparedFiniteScheduleUniformConditionalExcess_power_budget
    (s inputPower : ℕ) :
    ∃ extraPower : ℕ, 2 ≤ extraPower ∧
      ∀ m : ℕ, m ≤ s →
      ∀ {p Plate E : ℝ}, 2 ≤ p → 0 ≤ Plate →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ extraPower := by
  let exponent (m : ℕ) :=
    (exists_preparedFiniteScheduleConditionalExcess_power_budget m inputPower).choose
  let extraPower := 2 + ∑ j ∈ Finset.range (s + 1), exponent j
  refine ⟨extraPower, by dsimp only [extraPower]; omega, ?_⟩
  intro m hm p Plate E hp hPlate0 hPlate hE
  have hexponent : exponent m ≤ extraPower := by
    have hsum : exponent m ≤ ∑ j ∈ Finset.range (s + 1), exponent j :=
      Finset.single_le_sum (f := exponent) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp only [extraPower]
    omega
  have hlocal := (exists_preparedFiniteScheduleConditionalExcess_power_budget
    m inputPower).choose_spec.2 hp hPlate0 hPlate hE
  change preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ exponent m at hlocal
  exact hlocal.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hexponent)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedNestedFrontProjectionEnvelope
    {K : Type*} [Fintype K] (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) (outer inner : K → ℕ) (native : K → ℝ)
    (x gainLog stageLog endpoint : ℝ) : ℝ :=
  endpoint + 1 + ∑ k, preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
    (preparedFiniteForwardWork A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k)

theorem exists_preparedNestedFrontProjectionEnvelope_budget
    (A Cdirect Cnative : ℕ) (constants : ℕ → ℕ)
    (innerDepth outerDepth cardBound inputPower maxLayers : ℕ) (hA : 2 ≤ A) :
    ∃ projectionPower requiredPower : ℕ, 2 ≤ projectionPower ∧ 2 ≤ requiredPower ∧
      ∀ {K : Type*} [Fintype K] (outer inner : K → ℕ) (native : K → ℝ),
      Fintype.card K ≤ cardBound → (∀ k, outer k ≤ outerDepth) →
      (∀ k, inner k ≤ innerDepth) →
      ∀ {x gainLog stageLog endpoint Plate : ℝ}, 2 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      endpoint ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      Plate ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      (∀ k, native k ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision A Cdirect constants (inner k) false
          (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog +
          preparedFiniteForwardWork A constants (inner k)
            (candidateNestedForwardSeed A constants innerDepth (outer k) x) + Cnative) ^ Cnative)) →
      let E := preparedNestedFrontProjectionEnvelope A constants innerDepth
        outer inner native x gainLog stageLog endpoint
      E ∈ Set.Icc 0 ((x + 2) ^ projectionPower) ∧ endpoint ≤ E ∧
      (∀ k, preparedFiniteForwardFrontProjectionPrecision
        (preparedFiniteForwardModelPrecision A constants (inner k)
          (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
        (preparedFiniteForwardWork A constants (inner k)
          (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k) ≤ E) ∧
      ∀ m ≤ maxLayers,
        preparedConditionalExcessRequired m Plate E ≤ (x + 2) ^ requiredPower := by
  obtain ⟨D, _, hlocal⟩ := exists_candidateNestedForwardLocal_budget
    A Cdirect constants innerDepth outerDepth hA
  obtain ⟨C, _, hfront⟩ := exists_preparedFiniteForwardFrontProjection_budget Cnative
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ D
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower + 1 +
    Polynomial.C cardBound * (2 * B + Polynomial.C C) ^ C
  obtain ⟨projectionPower, hpPower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  obtain ⟨requiredPower, hrPower, hrequired⟩ :=
    exists_preparedFiniteScheduleUniformConditionalExcess_power_budget
      maxLayers (max inputPower projectionPower)
  refine ⟨projectionPower, requiredPower, hpPower, hrPower, ?_⟩
  intro K _ outer inner native hcard houter hinner x gainLog stageLog endpoint Plate
    hx hg hs hend hPlate hn E
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 2).trans hx
  let bound : ℝ := (x + 2) ^ D
  have hb0 : 0 ≤ bound := by dsimp only [bound]; positivity
  let entry := fun k => preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
    (preparedFiniteForwardWork A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k)
  have hentry : ∀ k, entry k ∈ Set.Icc 0 ((2 * bound + C) ^ C) := by
    intro k
    let seed := candidateNestedForwardSeed A constants innerDepth (outer k) x
    have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth (outer k) hx0
    have hxs : x ≤ seed := le_candidateNestedForwardSeed A constants innerDepth (outer k) hA hx0
    have hloc := hlocal hx0 hg hs (outer k) (houter k) (inner k) (hinner k)
    have hf := hfront A Cdirect constants (inner k) hseed
      ⟨hg.1, hg.2.trans hxs⟩ ⟨hs.1, hs.2.trans hxs⟩ (hn k)
    refine ⟨hf.1, hf.2.trans ?_⟩
    have hsource := hloc.2.2.2.2.2 false
    have hwork := hloc.2.2.1
    apply pow_le_pow_left₀
      (add_nonneg (add_nonneg hsource.1 hwork.1) (Nat.cast_nonneg C))
    dsimp only [bound] at hsource hwork ⊢
    linarith only [hsource.2, hwork.2]
  have hsum0 : 0 ≤ ∑ k, entry k := Finset.sum_nonneg (fun k _ => (hentry k).1)
  have hE0 : 0 ≤ E := by
    change 0 ≤ endpoint + 1 + ∑ k, entry k
    linarith only [hend.1, hsum0]
  have hsum : ∑ k, entry k ≤ (cardBound : ℝ) * (2 * bound + C) ^ C := by
    calc
      ∑ k, entry k ≤ ∑ _k : K, (2 * bound + C) ^ C :=
        Finset.sum_le_sum (fun k _ => (hentry k).2)
      _ = (Fintype.card K : ℝ) * (2 * bound + C) ^ C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
  have hE : E ≤ (x + 2) ^ projectionPower := by
    have htotal : (x + 2) ^ inputPower + 1 +
        (cardBound : ℝ) * (2 * bound + C) ^ C ≤ (x + 2) ^ projectionPower := by
      simpa [Q, B, bound, Polynomial.eval₂_pow] using hQ x hx0
    change endpoint + 1 + ∑ k, entry k ≤ _
    linarith only [hend.2, hsum, htotal]
  refine ⟨⟨hE0, hE⟩, ?_, ?_, ?_⟩
  · change endpoint ≤ endpoint + 1 + ∑ k, entry k
    linarith only [hsum0]
  · intro k
    have hk : entry k ≤ ∑ j, entry j :=
      Finset.single_le_sum (fun j _ => (hentry j).1) (Finset.mem_univ k)
    change entry k ≤ endpoint + 1 + ∑ j, entry j
    linarith only [hk, hend.1]
  · intro m hm
    exact hrequired m hm hx hPlate.1
      (hPlate.2.trans (pow_le_pow_right₀ (by linarith : 1 ≤ x + 2) (Nat.le_max_left _ _)))
      (hE.trans (pow_le_pow_right₀ (by linarith : 1 ≤ x + 2) (Nat.le_max_right _ _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteNestedSourceProjectionPrecision
    {outerDepth innerDepth cutoff : ℕ} (m : ℕ) (G : Type) [Fintype G]
    (count nX A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate endpoint : ℝ) : ℝ :=
  preparedNestedFrontProjectionEnvelope A constants innerDepth
    (fun k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff => k.1.val)
    (fun k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff => k.2.1.val)
    (preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate)
    Bstruct gainLog stageLog endpoint

theorem exists_preparedFiniteNestedSourceProjection_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ)
    (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ projectionPower requiredPower : ℕ, 2 ≤ projectionPower ∧ 2 ≤ requiredPower ∧
    ∀ (G : Type) [Fintype G] (count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Plate endpoint : ℝ},
      2 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Plate ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      let E := preparedFiniteNestedSourceProjectionPrecision
        (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
        m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint
      E ∈ Set.Icc 0 ((Bstruct + 2) ^ projectionPower) ∧ endpoint ≤ E ∧
        preparedConditionalExcessRequired m Plate E ≤ (Bstruct + 2) ^ requiredPower := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let Cnative := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
  obtain ⟨Cp, Cr, hCp, hCr, hbudget⟩ := exists_preparedNestedFrontProjectionEnvelope_budget
    A Cdirect Cnative constants innerDepth outerDepth (Fintype.card K) inputPower m hA
  refine ⟨Cp, Cr, hCp, hCr, ?_⟩
  intro G _ count nX Bstruct pnum Qstride gainLog stageLog Plate endpoint
    hB hnum hstride hg hs hcount hnX hG hend hPlate E
  let native : K → ℝ := preparedFiniteNestedSourceNative m G count nX
    (preparedFiniteForwardDetectorPolynomial cutoff) A Cdirect constants
    Bstruct pnum Qstride gainLog stageLog Plate
  have hnative (k : K) := preparedFiniteNestedSourceNative_budget m G count nX A Cdirect constants
    hcutoff hA ((by norm_num : (0 : ℝ) ≤ 2).trans hB) hnum hstride hg hs hcount hnX hG Plate k
  have h := hbudget (fun k : K => k.1.val) (fun k : K => k.2.1.val) native le_rfl
    (fun k => Nat.le_of_lt_succ k.1.isLt) (fun k => Nat.le_of_lt_succ k.2.1.isLt)
    hB hg hs hend hPlate (fun k => by
      simpa only [native, Cnative, preparedFiniteNestedForwardAllDegreeStage,
        preparedFiniteNestedForwardAllDegreeSeed, preparedFiniteNestedForwardAllDegreeOuter,
        preparedFiniteForwardPairedSourcePrecision_model] using hnative k)
  exact ⟨h.1, h.2.1, h.2.2.2 m le_rfl⟩

end Erdos3.VectorPolynomial

end

end OAI
