import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerExponentialLimit
import IPRADerivations.Analysis.RationalArithmetic.Complex.Arguments.GaussianRightHalfPlaneArgumentAxis
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerRealSamples

/-!
# The cofinal Euler logarithm on the positive rational axis

The zero phase branch returns the literal Gaussian zero. The radial
sampler, each finite logarithm row, and the finite head consequently
return real samples at their original clocks. Real exponential
injectivity identifies the resulting cofinal name with the existing
positive-rational logarithm of Gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerPositiveAxis

open_ipra
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaInputProperness (code_data_cross original_Gamma_proper)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianLogGammaEulerHead (argument rowData productF productData)
open GaussianLogGammaEulerFactorSum (residualF residualBody residual_at)
open GaussianLogGammaEulerNormalizedHead (denominatorF denominatorData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (canonical_congr ofGaussian_canonical positive_product qzero)
open GaussianRationalSyntheticDivision (qzero_canonical qmul_congr qmul_zero_right)
open GaussianRealNameExponentialInjectivity (axisSamples)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRootAlgebra (equal equal_of_values equal_symm re_scale im_scale re_one im_one)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingNames (add_real multiply_real constant_real)
open RationalGaussianEmbedding (axis axis_add axis_congr axis_zero subst_axis)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "RF" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "RD" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "AF" => GaussianRightHalfPlaneArgument.nameF
local notation "AD" => GaussianRightHalfPlaneArgument.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerCofinal.canonicalData
local notation "H" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "headData" => GaussianLogGammaEulerNormalizedHead.data
local notation "sumData" => GaussianNamedFiniteSumFamily.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "U" => GaussianNameBounds.U
local notation "J" => GaussianStirlingGammaLogarithm.logGammaF
local notation "jd" => GaussianStirlingGammaLogarithm.logGammaData
local notation "referenceSource" => GaussianStirlingGammaLogarithm.source
local notation "arg" => GaussianStirlingGammaLogarithm.arg
local notation "GammaF" => GaussianGammaReciprocalInverse.gammaF
local notation "gammaData" => GaussianGammaReciprocalInverse.gammaData

private theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A D neg : PTm n) :
    (source A D neg).subst σ = source (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ neg) := by simp [source]

open GaussianArctangentExponentialPrefix (prefixValue prefix_zero)
open GaussianArctangentPartialQuadrature (mesh clearing)
open GaussianRightHalfPlaneArgument (smallF smallData largeF largeData unsignedF unsignedData wide wide_zero)

private theorem small_phase_zero (p A : PTm n) :
    Γ ⊢[PRAAx] ap2 smallF p (smallData A zero) ≐ qzero := by
  let atanF := GaussianArctangentPartialQuadrature.nameF
  let x := GaussianArctangentPartialQuadrature.data zero A
  let j := GaussianBoundedConstantProductName.clock p one
  let M := A*mesh j
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF p one GaussianRightHalfPlaneArgument.half x
  have index : Γ ⊢[PRAAx] prefixValue (zero*mesh j) M (clearing M) ≐ prefixValue zero M (clearing M) := by
    simpa only [GaussianArctangentExponentialPrefix.subst_prefixValue,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (prefixValue (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![zero*mesh j,M,clearing M]) (σ' := ![zero,M,clearing M])
        (fun i => by fin_cases i; exact zero_mul _; exact .eqRefl _; exact .eqRefl _)
  have h := (GaussianArctangentPartialQuadrature.sample_at (Γ := Γ) j zero A).eqTrans
    (index.eqTrans (prefix_zero M (clearing M)))
  exact e.eqTrans ((qmul_congr (.eqRefl _) h).eqTrans (qmul_zero_right _))

theorem phase_sample_zero (p A neg : PTm n) (h : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] ap2 AF p (AD A zero neg) ≐ qzero := by
  let x := unsignedData A zero
  have inner := GaussianNameBranch.sample_at (Γ := Γ) smallF largeF p
    (wide A zero) (smallData A zero) (largeData A zero)
  have unsigned : Γ ⊢[PRAAx] ap2 unsignedF p x ≐ qzero :=
    inner.eqTrans ((RationalArithmetic.select_zero _ _ _ (wide_zero A zero (zero_le A))).eqTrans (small_phase_zero p A))
  have outer := GaussianNameBranch.sample_at (Γ := Γ) unsignedF (GaussianNameConjugation.nameF unsignedF) p neg x x
  refine h.orE ?_ ?_
  · exact outer.wk.eqTrans ((RationalArithmetic.select_zero _ _ _ Prf.hyp0).eqTrans unsigned.wk)
  · exact outer.wk.eqTrans ((RationalArithmetic.select_one _ _ _ Prf.hyp0).eqTrans
      ((GaussianNameConjugation.sample_at unsignedF p x).eqTrans
        ((GaussianRationalConjugation.point_congr unsigned.wk).eqTrans GaussianRationalConjugation.point_zero)))

private theorem positive_log_samples (a b : PTm n) :
    Γ ⊢[PRAAx] realSamples logF (L a b) := by
  refine .allI ?_
  simpa only [realSamples,Syn.shift,GaussianPositiveRationalLogarithm.subst_data,GaussianPositiveRationalLogarithm.sample] using
    (Prf.andI (GaussianPositiveRationalLogarithm.sample_canonical (Γ := Γ.map Fm.shift) (var 0) (Syn.shift a) (Syn.shift b))
      (GaussianPositiveRationalLogarithm.sample_axis (var 0) (Syn.shift a) (Syn.shift b)))

theorem logarithm_real_samples (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] realSamples G (P A zero D neg) := by
  let X := GaussianRightHalfPlaneRadialLogarithm.normNum A zero
  let Y := GaussianRightHalfPlaneRadialLogarithm.normDen D
  have radial : Γ ⊢[PRAAx] realSamples RF (RD A zero D) :=
    GaussianNamedHalf.real logF (L X Y) (positive_log_samples X Y)
  have phase : Γ ⊢[PRAAx] realSamples AF (AD A zero neg) := by
    refine .allI ?_
    let Δ := Γ.map Fm.shift
    have hg : Δ ⊢[PRAAx] source (Syn.shift A) (Syn.shift D) (Syn.shift neg) := by
      simpa only [Δ,Fm.shift,Syn.shift,subst_source] using h.shift
    have e := phase_sample_zero (Γ := Δ) (var 0) (Syn.shift A) (Syn.shift neg) hg.andE₁.andE₂
    simpa only [Δ,realSamples,Syn.shift,GaussianRightHalfPlaneArgument.subst_data,ConciseIPRA.PTm.subst_zero] using
      (Prf.andI (canonical_congr e qzero_canonical) (axis_congr e.eqSymm axis_zero))
  exact add_real RF AF (RD A zero D) (AD A zero neg) radial phase

private def rowAxes (t : PTm 2) (x : PTm n) : Fm PTm n :=
  .all (axis (inst2 t (var 0) (Syn.shift x)))

@[simp] private theorem subst_rowAxes {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x : PTm n) :
    (rowAxes t x).subst σ = rowAxes t (Syn.subst σ x) := by
  simp [rowAxes,Syn.subst_shift,Syn.shift_subst]

private theorem axis_row_at (t : PTm 2) (x i : PTm n) (h : Γ ⊢[PRAAx] rowAxes t x) :
    Γ ⊢[PRAAx] axis (inst2 t i x) := by
  simpa only [rowAxes,subst_axis,subst_inst2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem sum_axis (t : PTm 2) (m x : PTm n) (h : Γ ⊢[PRAAx] rowAxes t x) :
    Γ ⊢[PRAAx] axis (GaussianRationalFiniteSum.sum t m x) := by
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := axis (GaussianRationalFiniteSum.sum t (var 0) y)
  have hs : Δ ⊢[PRAAx] rowAxes t y := by simpa only [Δ,y,Fm.shift,Syn.shift,subst_rowAxes] using h.shift
  have all : Γ ⊢[PRAAx] .all motive := by
    refine PRA.qfInd _ (by simp [motive,axis,RationalArgmin.rationalEq,Fm.QF]) ?_ ?_
    · simpa only [motive,y,subst_axis,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (axis_congr (GaussianRationalFiniteSum.sum_zero (Γ := Γ) t x).eqSymm axis_zero)
    · simp only [motive,y,subst_axis,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact axis_congr (GaussianRationalFiniteSum.sum_succ t (var 0) y).eqSymm
        (axis_add _ _ Prf.hyp0 (axis_row_at t y (var 0) hs.wk))
  simpa only [motive,y,subst_axis,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

private theorem finite_residual_axis (k A D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] axis (GaussianNamedFiniteSumFamily.finite G residualBody k N (rowData A zero D neg)) := by
  let t := GaussianNamedFiniteSumFamily.body G residualBody
  let x := rowData A zero D neg
  apply sum_axis t N (pairT k x) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let j := succ i
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift
  have hr : Δ ⊢[PRAAx] source (sh A+j*sh D) (sh D*j) (sh neg) :=
    .andI (.andI (le_trans hs.andE₁.andE₁ (le_add_right _ _)) hs.andE₁.andE₂)
      (positive_product _ _ hs.andE₂ (zero_lt_succ i))
  have e := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) G residualBody i (sh k) (rowData (sh A) zero (sh D) (sh neg))).eqTrans
    (congrAp2 G (.eqRefl _) (residual_at i (sh A) zero (sh D) (sh neg)))
  have row := logarithm_real_samples (sh A+j*sh D) (sh D*j) (sh neg) hr
  simpa only [Δ,t,x,sh,i,j,Syn.shift,subst_pairT,GaussianLogGammaEulerHead.subst_rowData,ConciseIPRA.PTm.subst_zero] using
    axis_congr e.eqSymm (real_sample_at G _ (sh k) row).andE₂

theorem residual_real_samples (A D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] realSamples residualF (sumData N (rowData A zero D neg)) := by
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let x := rowData (sh A) zero (sh D) (sh neg)
  let k := GaussianFastValueCut.exponent (sh N) p
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift
  have e := GaussianNamedFiniteSumFamily.sample_at (Γ := Δ) G residualBody p (sh N) x
  have can := GaussianRationalFiniteSum.sum_canonical (Γ := Δ) (GaussianNamedFiniteSumFamily.body G residualBody) (sh N) (pairT k x)
  have ax := finite_residual_axis k (sh A) (sh D) (sh neg) (sh N) hs
  simpa only [Δ,realSamples,sh,x,p,Syn.shift,GaussianNamedFiniteSumFamily.subst_data,
    GaussianLogGammaEulerFactorSum.residualF,GaussianLogGammaEulerHead.subst_rowData,ConciseIPRA.PTm.subst_zero] using
    Prf.andI (canonical_congr e can) (axis_congr e.eqSymm ax)

open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open RationalArithmetic (select_zero select_one)

private theorem imaginary_at_zero (neg : PTm n) (h : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] ZT.eq (signedImag zero neg) (ZT.ofNat zero) := by
  refine h.orE ?_ ?_
  · let Δ := (neg ≐ zero) :: Γ
    have e := natEq (select_zero (Γ := Δ) neg zero zero Prf.hyp0)
    apply ZT.derive
    simp only [signedImag,ZT.toZ,ZT.ofNat]
    rw [e]
  · let Δ := (neg ≐ one) :: Γ
    have e := natEq (select_one (Γ := Δ) neg zero zero Prf.hyp0)
    apply ZT.derive
    simp only [signedImag,ZT.toZ,ZT.ofNat]
    rw [e]

theorem native_axis_equal (A neg : PTm n) (h : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] equal (native A zero neg) (arg A) := by
  have ee := ZT.toZ_eq (imaginary_at_zero neg h)
  apply equal_of_values
  · simp only [GaussianLogGammaEulerResidualDomain.native,GaussianStirlingGammaLogarithm.arg,eval_re_code,
      re_scale,re_one,ZT.toZ_ofNat]
    ring
  · simp only [GaussianLogGammaEulerResidualDomain.native,GaussianStirlingGammaLogarithm.arg,eval_im_code,
      im_scale,im_one,ZT.toZ_ofNat] at ee ⊢
    rw [ee]
    ipra_simps
    ring

theorem normalized_head_real_samples (A D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] realSamples H (headData A zero D neg N) := by
  let a := argument A zero D neg
  let x := sumData N (rowData A zero D neg)
  let y := P A zero D neg
  have e := GaussianGammaFiniteValueProperness.fraction_equal (native A zero neg) (arg A) D h.andE₂
    (native_axis_equal A neg h.andE₁.andE₂)
  have argAxis : Γ ⊢[PRAAx] axis a := axis_congr e.eqSymm (GaussianStirlingNames.fraction_axis A D h.andE₂)
  have c := constant_real a (ofGaussian_canonical (native A zero neg) D h.andE₂) argAxis
  have first := multiply_real constantF logF a (L N one) c (positive_log_samples N one)
  have second := add_real G residualF y x (logarithm_real_samples A D neg h) (residual_real_samples A D neg N h)
  have negative := GaussianNamedDampingPowerRealSamples.negative_real denominatorF (denominatorData A zero D neg N) second
  exact add_real productF (negativeF denominatorF) (productData A zero D neg N)
    (negativeData (denominatorData A zero D neg N)) first negative

theorem cofinal_real_samples (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] realSamples F (cofinalData A zero D neg) := by
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let R := radius (sh A) zero
  let N := GaussianLogGammaEulerCofinal.cutoff R p
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift
  have raw := real_sample_at H (headData (sh A) zero (sh D) (sh neg) N) (succ p)
    (normalized_head_real_samples (sh A) (sh D) (sh neg) N hs)
  have e : Δ ⊢[PRAAx] ap2 F p (cofinalData (sh A) zero (sh D) (sh neg)) ≐
      ap2 H (succ p) (headData (sh A) zero (sh D) (sh neg) N) :=
    GaussianLogGammaEulerCofinal.sample_at p (sh A) zero (sh D) (sh neg) R
  simpa only [Δ,realSamples,sh,p,Syn.shift,GaussianLogGammaEulerCofinal.subst_canonicalData,
    ConciseIPRA.PTm.subst_zero] using
    Prf.andI (canonical_congr e raw.andE₁) (axis_congr e.eqSymm raw.andE₂)

theorem cofinal_axis_samples (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] axisSamples F (cofinalData A zero D neg) := by
  have hr := cofinal_real_samples A D neg h
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples F (Syn.shift (cofinalData A zero D neg)) := by
    simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples] using hr.shift
  exact (real_sample_at F _ (var 0) hs).andE₂

private theorem gamma_radius_congr (z D R S : PTm n) (e : Γ ⊢[PRAAx] R ≐ S) :
    Γ ⊢[PRAAx] gammaData z R D D ≐ gammaData z S D D := by
  simpa only [GaussianGammaInverseConjugation.subst_original_gamma_data,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (gammaData (var 0) (var 1) (var 2) (var 2) : PTm 3)
      (σ := ![z,R,D]) (σ' := ![z,S,D]) (fun i => by fin_cases i; exact .eqRefl _; exact e; exact .eqRefl _)

theorem axis_exponential_gamma (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (E F) GammaF (GaussianLogGammaEulerExponentialLimit.expData A zero D neg)
      (GaussianStirlingGammaLogarithm.gammaData A D) := by
  let z := arg A
  let w := native A zero neg
  let R := radius A zero
  let x := gammaData w R D D
  let y := gammaData z R D D
  let t := gammaData z A D D
  have hs : Γ ⊢[PRAAx] referenceSource A D := .andI h.andE₁.andE₁ h.andE₂
  have hAR : Γ ⊢[PRAAx] le A R := le_add_right A zero
  have hR : Γ ⊢[PRAAx] le one R := le_trans hs.andE₁ hAR
  have hD : Γ ⊢[PRAAx] le A (R*D) := le_trans hAR
    (le_congr (one_mul R) (mul_comm D R) (mul_le_mul_right R h.andE₂))
  have ready := GaussianStirlingGammaLogarithm.gamma_source_at_radius A D R hs hR hD
  have same := original_Gamma_proper z w R D one D ready (equal_symm (native_axis_equal A neg h.andE₁.andE₂))
  have er : Γ ⊢[PRAAx] R ≐ A := add_zero A
  have bind := code_data_cross GammaF y t (GaussianGammaReciprocalInverse.gamma_regular z R D one D ready)
    (GaussianStirlingGammaLogarithm.gamma_regular A D hs) (gamma_radius_congr z D R A er)
  exact cross_trans (E F) GammaF GammaF _ x t (GaussianLogGammaEulerExponentialLimit.gamma_equivalent A zero D neg h)
    (cross_trans GammaF GammaF GammaF x y t (cross_symm GammaF GammaF y x same) bind)

theorem equivalent (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent F J (cofinalData A zero D neg) (jd A D) := by
  let x := cofinalData A zero D neg
  let y := jd A D
  let R := GaussianLogGammaEulerExponentialLimit.disk A zero D neg
  let S := U J y
  have hs : Γ ⊢[PRAAx] referenceSource A D := .andI h.andE₁.andE₁ h.andE₂
  have hf := GaussianGammaFiniteApproximantName.exponential_input F x (GaussianLogGammaEulerCofinal.canonical_regular A zero D neg h)
  have hi := GaussianExponentialRadiusIndependence.input_widen F (U F x) R x hf (le_add_right _ _)
  have hj := GaussianGammaFiniteApproximantName.exponential_input J y (GaussianStirlingGammaLogarithm.log_gamma_regular A D hs)
  have a := axis_exponential_gamma A D neg h
  have b := GaussianStirlingLogDuplication.exponential_gamma A D hs
  apply GaussianRealNameExponentialInjectivity.independent_radii_injective F J R S x y hi hj
    (cofinal_axis_samples A D neg h) (GaussianStirlingGammaLogarithm.log_gamma_axis A D)
  exact cross_trans (E F) GammaF (E J) (ed R x) _ (ed S y) a (cross_symm _ _ _ _ b)

theorem actual_cofinal_Euler_log_Gamma_is_real_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ realSamples F (cofinalData (var 0) zero (var 1) (var 2))) :=
  closeUniv 3 (.impI (cofinal_real_samples _ _ _ Prf.hyp0))

theorem actual_cofinal_Euler_log_Gamma_positive_axis_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ crossEquivalent F J (cofinalData (var 0) zero (var 1) (var 2)) (jd (var 0) (var 1))) :=
  closeUniv 3 (.impI (equivalent _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerPositiveAxis
