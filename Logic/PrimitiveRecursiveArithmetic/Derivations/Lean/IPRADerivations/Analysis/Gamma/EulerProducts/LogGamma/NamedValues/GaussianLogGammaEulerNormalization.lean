import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerRepresentation
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementLogGap

/-!
# Normalization of the cofinal Euler logarithm at one

The original denominator at one is the sum of the first N+1 positive
integer logarithms. Cancel the factorial logarithm from the actual
finite head and bound the remaining adjacent logarithm difference.
The cofinal sampler therefore represents exactly zero at one.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalization

open_ipra
open ComplexLogarithmRemainder (code oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (add_data_congr)
open GaussianLogGammaEulerHead (argument rowData rowBody row_at productF productData sumData)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameArithmetic (addF addData add_fast multiplyF)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (equivalent_of_envelope multiply_one_left oneF one_fast zeroF zero_at zero_fast)
open GaussianNamedDifference (sample_error)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (ofGaussian positive_product qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qone)
open GaussianRightHalfPlaneLogarithm (source)
open Products (fact)
open RationalArithmetic (select select_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "I" => GaussianLogGammaFactorialLogSum.logarithmBody
local notation "IF" => GaussianNamedFiniteSumFamily.nameF logF I
local notation "finiteData" => GaussianNamedFiniteSumFamily.data
local notation "F" => GaussianLogGammaEulerHead.nameF
local notation "headData" => GaussianLogGammaEulerHead.data
local notation "denominatorF" => GaussianLogGammaEulerHead.sumF
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "HL" => GaussianHarmonicLogarithmName.data
local notation "C" => GaussianLogGammaEulerCofinal.nameF

def oneData : PTm n := GaussianLogGammaEulerCofinal.canonicalData one zero one zero

@[simp] theorem subst_oneData {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (oneData : PTm n) = (oneData : PTm m) := by simp [oneData,one]

private theorem unit_source : Γ ⊢[PRAAx] source (one : PTm n) one zero :=
  .andI (.andI (le_refl _) (.orI₁ (.eqRefl _))) (le_refl _)

theorem argument_one : Γ ⊢[PRAAx] argument (one : PTm n) zero one zero ≐ qone := by
  change Γ ⊢[PRAAx] ofGaussian (code (ZT.ofNat one) ⟨select zero zero zero,select zero zero zero⟩) one ≐
    ofGaussian oneCode one
  unfold oneCode
  simpa only [GaussianRationalHorner.subst_ofGaussian,ComplexLogarithmRemainder.subst_code,ZT.subst,ZT.ofNat,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (ofGaussian (code (ZT.ofNat one) ⟨var 0,var 1⟩) one : PTm 2)
      (σ := ![select zero zero zero,select zero zero zero]) (σ' := ![zero,zero])
      (fun i => by fin_cases i <;> exact select_zero zero zero zero (.eqRefl _))

private theorem unit_product (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent productF logF (productData one zero one zero N) (L N one) := by
  let a : PTm n := argument one zero one zero
  let x := L N one
  have hx := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have constOne := GaussianArctangentExponentialPeriod.constant_one_cross (Γ := Γ) x
  have eq := cross_data_congr constantF oneF qone a x x argument_one.eqSymm (.eqRefl _) constOne
  exact GaussianNameRingLaws.multiply_unit_left constantF logF a x x (constant_regular a) hx eq

private theorem unit_rows (N : PTm n) :
    Γ ⊢[PRAAx] equalRows G logF rowBody I (succ N) (rowData one zero one zero) zero := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  let a : PTm (n+1) := one+j*one
  have ej : Δ ⊢[PRAAx] a ≐ succ j := by dsimp only [a]; ipra_ring
  have ha : Δ ⊢[PRAAx] le one a := le_add_right _ _
  have hs : Δ ⊢[PRAAx] source a one zero :=
    .andI (.andI ha (.orI₁ (.eqRefl _))) (le_refl _)
  have ax := GaussianRightHalfPlaneLogarithm.positive_axis a one zero hs
  have bound := row_at (Γ := Δ) j one zero one zero
  have rhs : Δ ⊢[PRAAx] L a one ≐ inst2 I j zero := by
    rw [GaussianLogGammaFactorialLogSum.logarithm_row]
    exact add_data_congr _ _ _ _ ej (.eqRefl _)
  have moved := cross_data_congr G logF _ _ _ _ bound.eqSymm rhs ax
  simpa only [Δ,j,Syn.shift,GaussianLogGammaEulerHead.subst_rowData,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ,one] using moved

private theorem unit_denominator (N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent denominatorF logF (sumData one zero one zero N) (L (fact (succ N)) one) :=
  cross_trans denominatorF IF logF _ (finiteData (succ N) zero) _
    (GaussianNamedFiniteSumFamilyCongruence.family_sum_cross G logF rowBody I (succ N) (rowData one zero one zero)
      zero (unit_rows N))
    (cross_symm logF IF _ _ (GaussianLogGammaFactorialLogSum.factorial_logarithm_cross (succ N) zero))

theorem factorial_successor (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent logF (addF logF logF) (L (fact (succ N)) one)
      (addData (L (fact N) one) (L (succ N) one)) := by
  let x : PTm n := zero
  let a := L (fact N) one
  let b := L (succ N) one
  let s := finiteData N x
  let t := finiteData (succ N) x
  have hs := GaussianNamedFiniteSumFamily.regular (Γ := Γ) logF I N x (GaussianLogGammaFactorialLogSum.logarithm_rows N x)
  have ha := GaussianPositiveRationalLogarithm.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hb := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (succ N) one (.andI (zero_lt_succ N) (le_refl one))
  have append := GaussianNamedFiniteSumFamilySplit.append_cross (Γ := Γ) logF I N x
    (GaussianLogGammaFactorialLogSum.logarithm_rows (succ N) x)
  rw [GaussianLogGammaFactorialLogSum.logarithm_row] at append
  have replace := add_cross IF logF logF logF s a b b hs ha hb hb
    (cross_symm logF IF _ _ (GaussianLogGammaFactorialLogSum.factorial_logarithm_cross N x))
    (cross_refl _ _ hb)
  exact cross_trans logF IF (addF logF logF) _ t _
    (GaussianLogGammaFactorialLogSum.factorial_logarithm_cross (succ N) x)
    (cross_trans IF (addF IF logF) (addF logF logF) _ _ _ append replace)

theorem original_head_at_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent F (diffF logF logF) (headData one zero one zero N)
      (diffData (L N one) (L (succ N) one)) := by
  let a := L (fact N) one
  let b := L N one
  let c := L (succ N) one
  let s := sumData one zero one zero N
  let t := productData one zero one zero N
  have hSource := unit_source (Γ := Γ)
  have ha := GaussianPositiveRationalLogarithm.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hb := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have hc := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (succ N) one (.andI (zero_lt_succ N) (le_refl one))
  have ht := GaussianLogGammaEulerNormalizedHead.product_regular one zero one zero N hN
  have hs := GaussianLogGammaEulerHead.sum_regular one zero one zero N hSource
  have first := add_cross logF logF productF logF a a t b ha ha ht hb (cross_refl _ _ ha) (unit_product N hN)
  have second := cross_trans (Γ := Γ) denominatorF logF (addF logF logF) s _ _ (unit_denominator N) (factorial_successor N)
  have reduce := difference_proper (addF logF productF) (addF logF logF) denominatorF (addF logF logF)
    (addData a t) (addData a b) s (addData a c) (add_fast _ _ _ _ ha ht) (add_fast _ _ _ _ ha hb)
    hs (add_fast _ _ _ _ ha hc) first second
  exact cross_trans F (diffF (addF logF logF) (addF logF logF)) (diffF logF logF) _ _ _
    reduce (GaussianBohrMollerupDifference.cancel_common logF logF logF a b c ha hb hc)

private theorem harmonic_gap (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 H p (HL N one)) (ap2 H p (HL (succ N) one))) qzero one N := by
  let u := ap2 H p (HL N one)
  let v := ap2 H p (HL (succ N) one)
  have hn : Γ ⊢[PRAAx] le two (succ N) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right one hN)
  have gap := GaussianStirlingGammaFractionalIncrementLogGap.log_gap (succ N) p hn
  have pred := pred_succ (Γ := Γ) N
  have exactGap : Γ ⊢[PRAAx] distanceBounded v u one N :=
    distance_congr (.eqRefl _) (congrAp2 H (.eqRefl _) (congrPairT pred (.eqRefl _))) (.eqRefl _) pred gap
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hN).iffMpr (distance_symmetric _ _ _ _ hN exactGap)

theorem original_head_error_at_one (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (headData one zero one zero N)) qzero
      (unit p+num 8*N) (N*unit p) := by
  let U := unit p
  let B := HL N one
  let D := HL (succ N) one
  let x := ap2 F p (headData one zero one zero N)
  let y := ap2 (diffF H H) p (diffData B D)
  let z := qsub (ap2 H p B) (ap2 H p D)
  have hp := unit_positive (Γ := Γ) p
  have hOld : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source N one := .andI hN (le_refl one)
  have hNew : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (succ N) one :=
    .andI (zero_lt_succ N) (le_refl one)
  have hb := GaussianHarmonicLogarithmName.name_regular N one hOld
  have hd := GaussianHarmonicLogarithmName.name_regular (succ N) one hNew
  have left := GaussianHarmonicLogarithmName.cross_original N one hOld
  have right := GaussianHarmonicLogarithmName.cross_original (succ N) one hNew
  have translate := difference_proper logF H logF H (L N one) B (L (succ N) one) D
    (GaussianPositiveRationalLogarithm.name_regular N one hOld) hb
    (GaussianPositiveRationalLogarithm.name_regular (succ N) one hNew) hd left right
  have eq := cross_trans F (diffF logF logF) (diffF H H) _ _ _ (original_head_at_one N hN) translate
  have cross := cross_at F (diffF H H) (headData one zero one zero N) (diffData B D) p p eq
  have small := distance_radius_mono x y _ _ two U (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) cross
  have raw := distance_triangle_same x y z two (num 6) U hp small (sample_error H H B D p hb hd)
  have both := GaussianRationalPanelTailDistance.triangle x z qzero (two+num 6) U one N hp hN
    raw (harmonic_gap p N hN)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [U]; ipra_ring)
    (by dsimp only [U]; ipra_ring) both

private theorem cofinal_at_one_diagonal (p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 C p oneData) (ap2 zeroF p zero) (num 13) (unit p) := by
  let R : PTm n := radius one zero
  let T := GaussianLogGammaEulerCofinal.cutoff R p
  let U := unit p
  let N := T+U
  let x := ap2 C p oneData
  let y := ap2 F p (headData one zero one zero N)
  have hT : Γ ⊢[PRAAx] le T N := le_add_right _ _
  have hp : Γ ⊢[PRAAx] le one U := unit_positive p
  have hN : Γ ⊢[PRAAx] le one N := le_trans (GaussianLogGammaEulerCofinal.cutoff_positive R p) hT
  have hlarge := le_trans (GaussianLogGammaEulerCofinal.cutoff_large R p) hT
  have hU : Γ ⊢[PRAAx] le U N := le_add_left _ _
  have cost : Γ ⊢[PRAAx] GaussianLogGammaEulerCofinal.cost R ≐ two := by
    dsimp only [R,GaussianLogGammaEulerCofinal.cost,radius]
    ipra_ring
  have left := GaussianLogGammaEulerCofinal.canonical_original_cutoff_distance p p one zero one zero N
    unit_source hN hlarge
  have leftSmall := distance_radius_mono x y _ _ (num 4) U
    (positive_product _ _ (positive_product _ _ hN hp) hp) hp
    (by
      dsimp only [R,U] at *
      have ec := natEq cost
      ipra_le 2*𝔞(unit p)*𝔞(unit p)*sl hU using linear_combination -(𝔞(unit p))^3*ec) left
  have right := original_head_error_at_one p N hN
  have rightSmall := distance_radius_mono y qzero _ _ (num 9) U (positive_product _ _ hN hp) hp
    (by dsimp only [U] at *; ipra_le 𝔞(unit p)*sl hU) right
  exact distance_congr (.eqRefl _) (zero_at p zero).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same x y qzero (num 4) (num 9) U hp leftSmall rightSmall)

theorem cofinal_at_one : Γ ⊢[PRAAx] crossEquivalent C zeroF (oneData : PTm n) zero := by
  refine equivalent_of_envelope C zeroF oneData zero (num 13)
    (GaussianLogGammaEulerCofinal.canonical_regular one zero one zero unit_source) (zero_fast zero) (.allI ?_)
  simpa only [Syn.shift,subst_oneData,ConciseIPRA.PTm.subst_zero,PTm.subst_num] using
    cofinal_at_one_diagonal (Γ := Γ.map Fm.shift) (var 0)

theorem at_represented_one (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ qone) : Γ ⊢[PRAAx]
    crossEquivalent C zeroF (GaussianLogGammaEulerCofinal.canonicalData A B D neg) zero :=
  cross_trans C C zeroF _ oneData _
    (GaussianLogGammaEulerRepresentation.canonical_cross A B D neg one zero one zero h unit_source
      (e.eqTrans argument_one.eqSymm)) cofinal_at_one

theorem actual_Euler_log_Gamma_at_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent C zeroF oneData zero :=
  cofinal_at_one

theorem actual_Euler_log_Gamma_at_represented_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 2) (var 3) ⟶ (argument (var 0) (var 1) (var 2) (var 3) ≐ qone) ⟶
        crossEquivalent C zeroF (GaussianLogGammaEulerCofinal.canonicalData (var 0) (var 1) (var 2) (var 3)) zero) :=
  closeUniv 4 (.impI (.impI (at_represented_one _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_Euler_log_Gamma_at_one_finite_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (var 0) ⟶ crossEquivalent F (diffF logF logF) (headData one zero one zero (var 0))
        (diffData (L (var 0) one) (L (succ (var 0)) one))) :=
  closeUniv 1 (.impI (original_head_at_one _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalization
