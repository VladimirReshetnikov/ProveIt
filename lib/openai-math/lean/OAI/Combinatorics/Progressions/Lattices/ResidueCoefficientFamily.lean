import OAI.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
import OAI.Combinatorics.Progressions.Linear.KernelCoefficientDensity
import OAI.Combinatorics.Progressions.Sampling.CoefficientGridRate

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientLogAllowance (j d : ℕ) (b : ℝ) : ℝ :=
  2*(j : ℝ)^2 + (2*j+4)*b + (j+2*d)*(b+4) + 4

theorem coefficientMeshConstant_le_exp (j d : ℕ) {R C b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hR : R ≤ Real.exp b) (hC : C ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) :
    2 * (1 + (2*R+2)^(j+d) * K) * (j.factorial * C^j) ≤
      Real.exp (coefficientLogAllowance j d b) := by
  have hone : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbox : 2*R+2 ≤ Real.exp (b+4) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (Real.exp_pos b).le]
  let Q := ((j : ℝ)+d)*(b+4)+b
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hterm : (2*R+2)^(j+d) * K ≤ Real.exp Q := by
    calc
      _ ≤ (Real.exp (b+4))^(j+d) * Real.exp b := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp only [Q, Nat.cast_add]
  have hD : (j.factorial : ℝ)*C^j ≤ Real.exp ((j : ℝ)^2+j*b) := by
    calc
      _ ≤ Real.exp ((j : ℝ)^2)*(Real.exp b)^j := by gcongr; exact factorial_le_exp_sq j
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have hfront : 2 * (1 + (2*R+2)^(j+d) * K) ≤ Real.exp (Q+4) := by
    calc
      _ ≤ 4*Real.exp Q := by linarith [Real.one_le_exp_iff.mpr hQ]
      _ ≤ Real.exp Q * Real.exp 4 := by nlinarith [Real.exp_pos Q]
      _ = _ := (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp (Q+4)*Real.exp ((j : ℝ)^2+j*b) :=
      mul_le_mul hfront hD (by positivity) (Real.exp_pos _).le
    _ = Real.exp (Q+4+((j : ℝ)^2+j*b)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp only [Q, coefficientLogAllowance]
      nlinarith [sq_nonneg (j : ℝ),
        mul_nonneg (show (0 : ℝ) ≤ j+3 by positivity) hb,
        mul_nonneg (show (0 : ℝ) ≤ d by positivity) (show 0 ≤ b+4 by positivity)]

theorem enormousCoefficient_tolerance_arithmetic {D H ε : ℝ}
    (hD : 0 ≤ D) (hH : 0 < H) (hε : 0 < ε)
    (hlarge : D * (1 + ε⁻¹) ≤ H) : D ≤ H ∧ D / H ≤ ε := by
  have hmul : 0 ≤ D * ε⁻¹ := by positivity
  constructor
  · nlinarith
  · apply (div_le_iff₀ hH).mpr
    have h := mul_le_mul_of_nonneg_right hlarge hε.le
    have he : D * (1+ε⁻¹) * ε = D*ε+D := by
      field_simp
    rw [he] at h
    nlinarith [mul_nonneg hD hε.le]

theorem affineCoefficientImage_tolerance {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR0 : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
      (1+ε⁻¹) * L^(h*(Fintype.card I+1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S, ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR0 hsupport) hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
            (affineProductProfile c w)) v| ≤ ε := by
  let j := Fintype.card I
  let d := Fintype.card (UnselectedColumn s)
  let B := affineCoefficientCommonBudget (Fintype.card J) d b t
  let E := coefficientLogAllowance j d B
  have hB : 0 ≤ B := affineCoefficientCommonBudget_nonneg _ _ hb ht
  have hbounds := affineCoefficientCommonBudget_bounds (Fintype.card J) d hb ht
  have hbB : Real.exp b ≤ Real.exp B := Real.exp_le_exp.mpr hbounds.1
  have hK : (affineProductProfileLip J δ : ℝ) ≤ Real.exp B :=
    (affineProductProfileLip_le_exp J hi).trans (Real.exp_le_exp.mpr hbounds.2.1)
  have hmesh := coefficientMeshConstant_le_exp j d (affineProductProfileLip J δ)
    hB hR0 hC0 (hR.trans hbB) (hC.trans hbB) hK
  have herror := affineCoefficientConstants_le_exp j d J hδ hb ht hi hG0 hU0 hC0 hR0 hG hU hC hR
  have hscale : (Real.exp E * L^(h*(j+1))) * (1+ε⁻¹) ≤ H := by
    calc
      _ = Real.exp E * (1+ε⁻¹) * L^(h*(j+1)) := by ring
      _ ≤ H := hlarge
  have harith := enormousCoefficient_tolerance_arithmetic (by positivity) hH hε hscale
  have hready : 2 * (1+(2*R+2)^(j+d)*affineProductProfileLip J δ) * (j.factorial*C^j) *
      L^(h*(j+1)) ≤ H :=
    (mul_le_mul_of_nonneg_right hmesh (by positivity)).trans harith.1
  obtain ⟨hZ, herr⟩ := affineCoefficientImage_enormous_error A s S hS h ctrl hL hH hC0 c w hw
    hδ hwidth hR0 hsupport hready
  refine ⟨hZ, fun v => (herr v).trans ?_⟩
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right herror (by positivity)) hH.le).trans harith.2

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientReplacementScale {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (b t ε L : ℝ) (h : ℕ) : ℝ :=
  Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
    (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
      (1+ε⁻¹) * L^(h*(Fintype.card I+1))

theorem affineCoefficientImage_residue_tolerance {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : CoefficientFiberControl (Matrix.fromCols A C) (s.trans Function.Embedding.inl)
      (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (hr : integerResidueMatrix C m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T), ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF (Matrix.fromCols A C) (affineProductProfile c w)
          (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
          (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
        coefficientResidueMultiplier A r v *
          kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH) C T c w
            (fun i => (v i : ℝ)/H)| ≤ ε := by
  obtain ⟨hZ, herr⟩ := affineCoefficientImage_tolerance (Matrix.fromCols A C)
    (s.trans Function.Embedding.inl) (Sum.elim S T) (Sum.rec hS hT) h ctrl hL hH hB0 hU0 hG0
    c w hw hδ hwidth R.coe_nonneg hsupport hb ht hε hG hU hB hR hi hlarge
  refine ⟨hZ, fun v => ?_⟩
  have he := herr v
  rw [coefficientImageMask_eq_multiplier,
    selectedCoefficientDensity_eq_kernel A s hA S (fun _ => H) hS (fun _ => hH) C T hT
      ctrl.det_ne_zero c w hδ hwidth R hsupport,
    coefficientImageMultiplier_eq_residue A C m r hperiod hr] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def coefficientGridReplacementScale {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (C R b t ε L : ℝ) (h : ℕ) : ℝ :=
  coefficientReplacementScale s b t
    (ε / coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R) L h

theorem coefficientGridReplacementScale_eq {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (C R b t ε L : ℝ) (h : ℕ) :
    coefficientGridReplacementScale s C R b t ε L h =
      Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
        (1 + coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R / ε) *
        L ^ (h * (Fintype.card I + 1)) := by
  simp only [coefficientGridReplacementScale, coefficientReplacementScale, inv_div]

theorem affineCoefficientGrid_tolerance {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hH1 : 1 ≤ H) (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR0 : 0 ≤ R)
    (hsupport : ∀ j, |c j| + w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientGridReplacementScale s C R b t ε L h ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S,
      (∫ v, |(coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR0 hsupport) hZ v).toReal -
        coefficientGridProxy A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
          (affineProductProfile c w) v| ∂Measure.count) ≤ ε := by
  have hbox := coefficientGridBoxFactor_pos (Fintype.card I) (Fintype.card J) hC0 hR0
  obtain ⟨hZ, he⟩ := affineCoefficientImage_tolerance A s S hS h ctrl hL hH hC0 hU0 hG0
    c w hw hδ hwidth hR0 hsupport hb ht (div_pos hε hbox) hG hU hC hR hi hlarge
  refine ⟨hZ, (coefficientImage_l1_of_control A s S hS h ctrl hH hH1 hC0
    (affineProductProfile c w) (affineProductProfile_nonneg c w hw) hR0
    (affineProductProfile_zero_outside c w hw hR0 hsupport) hZ he).trans_eq ?_⟩
  field_simp [hbox.ne']

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_average {Ω I J N : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights Ω)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Ω → Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : ∀ ω, p.weight ω ≠ 0 → CoefficientFiberControl (Matrix.fromCols A (C ω))
      (s.trans Function.Embedding.inl) (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε η : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε) (hη : 0 ≤ η)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : ∀ ω, p.weight ω ≠ 0 → integerResidueMatrix (C ω) m = r)
    (target : (I → ℝ) → ℝ)
    (hquad : ∀ v : I → ℤ,
      |p.mean (fun ω => kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
        (C ω) T c w (fun i => (v i : ℝ)/H)) - target (fun i => (v i : ℝ)/H)| ≤ η) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T), ∀ v,
      |p.mean (fun ω => H ^ Fintype.card I *
        (coefficientImagePMF (Matrix.fromCols A (C ω)) (affineProductProfile c w)
          (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
          (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal) -
        coefficientResidueMultiplier A r v * target (fun i => (v i : ℝ)/H)| ≤ ε+G*η := by
  obtain ⟨ω₀, hω₀⟩ := finiteProbability_exists_nonzero_weight p
  obtain ⟨hZ, _⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω₀) S T hS hT h (ctrl ω₀ hω₀)
    hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
    m r hperiod (hr ω₀ hω₀)
  refine ⟨hZ, fun v => ?_⟩
  have hmask := coefficientResidueMultiplier_bounds A (C ω₀) m r hperiod (hr ω₀ hω₀)
    (ctrl ω₀ hω₀).index_bound v
  apply finiteMean_masked_comparison_of_support p _ _ hmask.1 hmask.2 hη _ (hquad v)
  intro ω hω
  obtain ⟨_, herr⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω) S T hS hT h (ctrl ω hω)
    hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
    m r hperiod (hr ω hω)
  exact herr v

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_family {Ω I J N : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights Ω)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Ω → Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : ∀ ω, p.weight ω ≠ 0 → CoefficientFiberControl (Matrix.fromCols A (C ω))
      (s.trans Function.Embedding.inl) (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : ∀ ω, p.weight ω ≠ 0 → integerResidueMatrix (C ω) m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T),
      (∀ v, 0 ≤ coefficientResidueMultiplier A r v ∧ coefficientResidueMultiplier A r v ≤ G) ∧
      ∀ ω, p.weight ω ≠ 0 → ∀ v,
        |H ^ Fintype.card I *
          (coefficientImagePMF (Matrix.fromCols A (C ω)) (affineProductProfile c w)
            (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
            (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
          coefficientResidueMultiplier A r v *
            kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
              (C ω) T c w (fun i => (v i : ℝ)/H)| ≤ ε := by
  obtain ⟨ω₀, hω₀⟩ := finiteProbability_exists_nonzero_weight p
  obtain ⟨hZ, _⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω₀) S T hS hT h (ctrl ω₀ hω₀)
    hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
    m r hperiod (hr ω₀ hω₀)
  refine ⟨hZ, ?_, ?_⟩
  · exact coefficientResidueMultiplier_bounds A (C ω₀) m r hperiod (hr ω₀ hω₀)
      (ctrl ω₀ hω₀).index_bound
  · intro ω hω v
    obtain ⟨_, herr⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω) S T hS hT h (ctrl ω hω)
      hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
      m r hperiod (hr ω hω)
    exact herr v

end Erdos3

end

end OAI
