/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Dynamics.BooleanInputLogBudget
import OAI.Combinatorics.Progressions.Estimates.ActiveProfileNoise

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def booleanMassToleranceC2 {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (Wsum : ℝ) : ℝ :=
  polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree + 1) (booleanJetMassBudget (Fintype.card α) degree Wsum)

noncomputable def booleanMassPerturbationScale {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0)
    (degree : ℕ) (Wsum ε : ℝ) : ℝ :=
  polynomialPerturbationScale
    (jointBooleanInverseBudget (O := O) (α := α) h C (booleanToleranceMinor (O := O) (α := α) h c₀ ε))
    (booleanMassToleranceC2 (B := B) (α := α) Z h degree Wsum)
    (booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε)
    (ε / 2) (Fintype.card (Σ d, O d))

theorem booleanMassToleranceC2_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {Wsum : ℝ} (hWsum : 0 ≤ Wsum) :
    0 ≤ booleanMassToleranceC2 (B := B) (α := α) Z h degree Wsum :=
  polynomialMassC2Budget_nonneg _ _ (booleanJetMassBudget_nonneg _ _ hWsum)

theorem booleanMassToleranceC2_le_exp {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {Wsum P V : ℝ} (hWsum : 0 ≤ Wsum) (hV : 0 ≤ V)
    (hW : Wsum ≤ Real.exp P)
    (hN : (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)) : ℝ) ≤ Real.exp V) :
    booleanMassToleranceC2 (B := B) (α := α) Z h degree Wsum ≤
      Real.exp (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) := by
  simpa only [booleanMassToleranceC2, Nat.cast_add, Nat.cast_one] using polynomialMassC2Budget_le_exp
    (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) (degree + 1)
    hV (booleanJetMassBudget_nonneg _ _ hWsum) hN (booleanJetMassBudget_le_exp _ _ hWsum hW)

theorem booleanMassPerturbationScale_inverse_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (A T : ℝ≥0) (degree : ℕ)
    {Wsum ε P : ℝ} (hWsum : 0 ≤ Wsum) (hε : 0 < ε) (hP : 0 ≤ P)
    (hm : (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp P)
    (hK : (jointBooleanInverseBudget (O := O) (α := α) h C
      (booleanToleranceMinor (O := O) (α := α) h c₀ ε) : ℝ) ≤ Real.exp P)
    (hM : booleanMassToleranceC2 (B := B) (α := α) Z h degree Wsum ≤ Real.exp P)
    (hQ : booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε ≤ Real.exp P)
    (hεP : (ε / 2)⁻¹ ≤ Real.exp P) :
    (booleanMassPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Wsum ε)⁻¹ ≤
      Real.exp (6 * P + 8) :=
  polynomialPerturbationScale_inverse_le_exp (by positivity)
    (booleanMassToleranceC2_nonneg Z h degree hWsum)
    (booleanToleranceDivergence_nonneg h hh c₀ C hc₀ hC A T hε)
    (half_pos hε) hP _ hm hK hM hQ hεP

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def booleanMassInputLog (h : D → ℕ) (degree : ℕ) (P E V : ℝ) : ℝ :=
  let E' := E + Fintype.card D + 3
  jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
    jointBooleanInverseLog (O := O) (α := α) h P E' +
    (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
    Fintype.card (Σ d, O d) + E + 3

theorem booleanMassInputLog_nonneg (h : D → ℕ) (degree : ℕ) {P E V : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hV : 0 ≤ V) :
    0 ≤ booleanMassInputLog (B := B) (O := O) (α := α) h degree P E V := by
  have hE' : 0 ≤ E + Fintype.card D + 3 := by positivity
  have := jointBooleanPerturbationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE'
  unfold booleanMassInputLog booleanJetMassLog
  positivity

theorem booleanMassPerturbationScale_input_le_exp [DecidableEq α] [∀ d, Nonempty (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (degree : ℕ) {Wsum ε P E V : ℝ}
    (hWsum : 0 ≤ Wsum) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hWP : Wsum ≤ Real.exp P) (hεE : ε⁻¹ ≤ Real.exp E)
    (hNV : (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)) : ℝ) ≤ Real.exp V) :
    (booleanMassPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Wsum ε)⁻¹ ≤
      Real.exp (6 * booleanMassInputLog (B := B) (O := O) (α := α) h degree P E V + 8) := by
  let E' := E + Fintype.card D + 3
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hK0 := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE'
  have hQ0 := jointBooleanPerturbationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have hM0 : 0 ≤ 2 * V + 2 * ((degree : ℝ) + 1) +
      booleanJetMassLog (Fintype.card α) degree P + 2 := by
    unfold booleanJetMassLog
    positivity
  have hηE : ((ε / 4) / ((Fintype.card D : ℝ) + 1))⁻¹ ≤ Real.exp E' := by
    rw [inv_div, div_div_eq_mul_div, div_eq_mul_inv]
    calc
      _ ≤ (Real.exp (Fintype.card D) * Real.exp 3) * Real.exp E := by
        gcongr
        · exact Real.add_one_le_exp _
        · linarith [Real.add_one_le_exp (3 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [E']; ring
  have hη : ∀ _d : D, 0 < (ε / 4) / ((Fintype.card D : ℝ) + 1) := by
    intro d
    positivity
  have hK := jointBooleanInverseBudget_canonical_le_exp (O := O) (α := α)
    h hh c₀ C (fun _ => (ε / 4) / ((Fintype.card D : ℝ) + 1)) hc₀ hC hη
    hP hE' hcP hCP (fun _ => hηE)
  have hM := booleanMassToleranceC2_le_exp (B := B) (α := α) Z h degree hWsum hV hWP hNV
  have hQ := booleanToleranceDivergence_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C hc₀ hC hε hP hE' hcP hCP hηE A T hAP hTP
  have hm : (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp (Fintype.card (Σ d, O d) : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card (Σ d, O d) : ℝ)]
  have ha : (ε / 2)⁻¹ ≤ Real.exp (E + 1) := by
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1 * Real.exp E := by
        gcongr
        linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = _ := by rw [← Real.exp_add, add_comm]
  apply booleanMassPerturbationScale_inverse_le_exp Z h hh c₀ C hc₀ hC A T degree hWsum hε
    (booleanMassInputLog_nonneg h degree hP hE hV)
  · apply hm.trans
    apply Real.exp_le_exp.mpr
    unfold booleanMassInputLog
    change _ ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
      jointBooleanInverseLog (O := O) (α := α) h P E' +
      (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
      Fintype.card (Σ d, O d) + E + 3
    linarith
  · apply hK.trans
    apply Real.exp_le_exp.mpr
    unfold booleanMassInputLog
    change _ ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
      jointBooleanInverseLog (O := O) (α := α) h P E' +
      (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
      Fintype.card (Σ d, O d) + E + 3
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  · apply hM.trans
    apply Real.exp_le_exp.mpr
    unfold booleanMassInputLog
    change _ ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
      jointBooleanInverseLog (O := O) (α := α) h P E' +
      (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
      Fintype.card (Σ d, O d) + E + 3
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  · apply hQ.trans
    apply Real.exp_le_exp.mpr
    unfold booleanMassInputLog
    change _ ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
      jointBooleanInverseLog (O := O) (α := α) h P E' +
      (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
      Fintype.card (Σ d, O d) + E + 3
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  · apply ha.trans
    apply Real.exp_le_exp.mpr
    unfold booleanMassInputLog
    change _ ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E' +
      jointBooleanInverseLog (O := O) (α := α) h P E' +
      (2 * V + 2 * ((degree : ℝ) + 1) + booleanJetMassLog (Fintype.card α) degree P + 2) +
      Fintype.card (Σ d, O d) + E + 3
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_random_coefficient_mass_tolerance_with_scale
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ}
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Wsum : ℝ} (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanMassPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Wsum ε ∧
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex t (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  let η : D → ℝ := fun _ => (ε / 4) / ((Fintype.card D : ℝ) + 1)
  have hη (d : D) : 0 < η d := by dsimp [η]; positivity
  have hsum : (∑ d, η d) ≤ ε / 4 := by
    simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
  have hκ (d : D) : 0 < κ d := canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)
  let r := fun d (_ : B d × Fin (h d)) =>
    scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  have hr (d : D) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))
  let Kinv := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let Hderiv := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
  have hS : 0 ≤ S := jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le)
    κ (fun d => (hκ d).le)
  let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree + 1) (booleanJetMassBudget (Fintype.card α) degree Wsum)
  have hM : 0 ≤ M := polynomialMassC2Budget_nonneg _ _ (booleanJetMassBudget_nonneg _ _ hWsum)
  let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
    ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let t := polynomialPerturbationScale Kinv M Q (ε / 2) (Fintype.card (Σ d, O d))
  have ht := polynomialPerturbationScale_spec Kinv.coe_nonneg hM hQ (half_pos hε) (Fintype.card (Σ d, O d))
  refine ⟨t, ht.1, ht.2.1, rfl, ?_⟩
  intro μ hμ hbox hclow hcup P hP φ hφ hbound
  have he := random_coefficient_array_mass_comparison c hc z hz sets hsets h hh hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex
    inputIndex htaildegree hWsum hwsum η hη Kinv Hderiv
    (jointBooleanInverseBudget_le h C κ) (jointBooleanDerivativeBudget_le h C)
    t ht.1 ht.2.2.1 ht.2.2.2.1 μ hμ hbox hclow hcup P hP φ hφ hbound
  calc
    _ ≤ 2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := he
    _ ≤ ε / 2 + ε / 2 := add_le_add (by linarith) ht.2.2.2.2
    _ = ε := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_random_coefficient_mass_smaller_tolerance_with_scale
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ}
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Wsum : ℝ} (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanMassPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Wsum ε ∧
      ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex s (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨t, ht, ht1, hteq, _⟩ := exists_random_coefficient_mass_tolerance_with_scale
    (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone
    A T hLip hTransition terms weight exponent coefficientIndex inputIndex htaildegree
    hWsum hwsum hε
  refine ⟨t, ht, ht1, hteq, ?_⟩
  intro s hs
  have hratio : |s / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    exact (div_le_one ht).mpr hs
  have hw : ∀ d, (∑ n ∈ terms d, |(s / t) * weight d n|) ≤ Wsum :=
    fun d => coefficientTailWeightSum_scale_le (terms d) (weight d) hratio (hwsum d)
  obtain ⟨t', _, _, ht'eq, hcomp⟩ := exists_random_coefficient_mass_tolerance_with_scale
    (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone
    A T hLip hTransition terms (fun d n => (s / t) * weight d n) exponent coefficientIndex inputIndex
    htaildegree hWsum hw hε
  have hsame : t' = t := ht'eq.trans hteq.symm
  subst t'
  rw [← hteq] at hcomp
  have hcancel : t * (s / t) = s := by field_simp
  intro μ hμ hbox hclow hcup P hP φ hφ hbound
  simpa only [coefficientArraySampler_scale_weight, hcancel] using
    hcomp μ hμ hbox hclow hcup P hP φ hφ hbound

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem partitioned_profile_mass_comparison_below
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) {ε : ℝ} (hε : 0 < ε) :
    let t := booleanMassPerturbationScale (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h P) (fun d : {d // ¬P d} => h d.val)
      (fun d => unitProfilePrincipalSize (B := B) d.val)
      (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 ε
    0 < t ∧ t ≤ 1 ∧
      ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : Ω × ((Σ d, O d) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))) -
        ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R s (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  obtain ⟨t, ht, ht1, hteq, hcomp⟩ := exists_random_coefficient_mass_smaller_tolerance_with_scale
    (Y := Ω × ((Σ d, O d) → ℝ)) c hc z hz sets hsets (fun d : {d // ¬P d} => h d.val)
    (fun d => hh d.val) hcard block hblock
    (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    (fun d => unitProfilePrincipalSize_pos (B := B) d.val)
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d.val).le)
    ψ hψ hrange hzero hone A T hLip hTransition
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d e _ => e.property.trans (hdegree d.val))
    (Wsum := 1) zero_le_one (partitionedProfileTail_unit_sum h P) hε
  dsimp only
  rw [← hteq]
  refine ⟨ht, ht1, ?_⟩
  intro s hs μ hμ hbox R f hf hfb
  have hclow : ∀ᵐ a ∂μ, ∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)| := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).1
  have hcup : ∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).2
  let F : Ω × ((Σ d, O d) → ℝ) → Ω × ((Σ d, O d) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d, O d) → ℝ) → Ω))
    dsimp [F, booleanConstantJet, partitionedProfileConstant]
    split_ifs <;> fun_prop
  have hFactual (s : ℝ) (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, coefficientArraySampler (fun d : {d // ¬P d} => h d.val) (c a) sets
        (partitionedProfileTerms (G := G) (B := B) h P)
        (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
        (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra) s (z a) x) =
      (a, partitionedAllocatedProfileJet h P extra sets R s (z a) x) := by
    apply Prod.ext
    · rfl
    dsimp only [F]
    rw [partitionedAllocatedProfileJet_scale]
    unfold partitionedAllocatedProfileJet
    rw [partitionedProfileJet_eq h P extra sets hh]
    rfl
  have hFzero (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets x) =
        (a, partitionedAllocatedProfileJet h P extra sets R 0 (z a) x) := by
    simpa only [coefficientArraySampler_zero] using hFactual 0 a x
  simpa only [hFzero, hFactual] using hcomp s hs μ hμ hbox hclow hcup F hF f hf hfb

end Erdos3

end

end OAI
