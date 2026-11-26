import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductScaledArguments
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionSinePositive

/-!
# Scaling and phase identities for the actual sine-product arguments

Multiplying the actual name of πz/(Bm) by the natural number m yields
the actual name of πz/B. The real root argument kπ/m, rotated by i,
agrees with the divided-angle name already used for the original sine.
Both comparisons allow the programs to keep their independent clocks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductScaledArgumentIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineProductScaledArguments (coefficient nameF data name_regular observation_bound_at natural_code_bound)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianBoundedConstantProductName (clock)
open ComplexLogarithmRemainder (scale mul oneCode eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianRationalHorner (qmul ofGaussian ofGaussian_represents ofGaussian_canonical qmul_canonical qmul_represents
  canonical_unique represents_rescale represents_congr positive_product)
open GaussianRootAlgebra (equal_of_values equal_refl re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open GaussianRationalNaturalScale (natScale natScale_canonical natScale_represents natScale_product natScale_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNamedSineTaylor (imaginaryF imaginary_at imaginary_input)
open GaussianNamedSineFromExponential (sineF sineData sine_proper)
open GaussianRadiusExponentialName (input)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem wide_input (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] input nameF (num 4*R) (data z R B m x) := by
  refine .andI (name_regular z R B m x hB hm hz) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let z' := Syn.shift z
  let R' := Syn.shift R
  let B' := Syn.shift B
  let m' := Syn.shift m
  let x' := Syn.shift x
  have hB' : Δ ⊢[PRAAx] le one B' := by simpa [Fm.shift,Syn.shift,Δ,B',one] using hB.shift
  have hm' : Δ ⊢[PRAAx] le one m' := by simpa [Fm.shift,Syn.shift,Δ,m',one] using hm.shift
  have hz' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z' (R'*B') := by
    simpa [Fm.shift,Syn.shift,Δ,z',R',B'] using hz.shift
  have b := observation_bound_at z' R' B' m' x' (var 0) hB' hm' hz'
  have res := bounded_radius_mono _ _ _ (num 4*R') one hm' (le_refl one)
    (le_mul_mono (le_refl (num 4*R')) hm') b
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,GaussianSineProductScaledArguments.subst_data,
    PTm.subst_mul,PTm.subst_num,Δ,z',R',B',m',x'] using res

theorem coefficient_multiple (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] natScale m (coefficient z B m) ≐ coefficient z B one := by
  let a := scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) z)
  have hD := positive_product B m hB hm
  have h1 := positive_product B one hB (le_refl one)
  have left := natScale_represents m (coefficient z B m) a (B*m) hD (ofGaussian_represents _ _ hD)
  have right := represents_rescale (coefficient z B one) a (B*one) m (ofGaussian_represents _ _ h1)
  exact canonical_unique _ _ _ _ (natScale_canonical _ _) (ofGaussian_canonical _ _ h1) hD left
    (represents_congr (.eqRefl _) (equal_refl _) (by ipra_ring) right)

private theorem bounded_clock_later (p A : PTm n) : Γ ⊢[PRAAx] le p (clock p A) :=
  le_add_right _ _

def scaleF : PR 2 := GaussianNamedNaturalScale.nameF nameF
def scaleData (z R B m E x : PTm n) : PTm n := GaussianNamedNaturalScale.data E m (data z R B m x)

@[simp] theorem subst_scaleData {l : ℕ} (σ : Fin n → PTm l) (z R B m E x : PTm n) :
    Syn.subst σ (scaleData z R B m E x) =
      scaleData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ E) (Syn.subst σ x) := by
  simp [scaleData]

theorem multiple_sample_at (z R B m E x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 scaleF p (scaleData z R B m E x) ≐ qmul (coefficient z B one)
      (ap2 quarterF (clock (GaussianNamedNaturalScale.clock p E) (two*R)) x) := by
  let s := GaussianNamedNaturalScale.clock p E
  let Q := ap2 quarterF (clock s (two*R)) x
  let c := coefficient z B m
  have scaleSwap : Γ ⊢[PRAAx] natScale m (qmul c Q) ≐ qmul (natScale m c) Q :=
    (natScale_congr (.eqRefl _) (qmul_commutative c Q)).eqTrans
      ((natScale_product m Q c).eqSymm.eqTrans (qmul_commutative Q _))
  exact (GaussianNamedNaturalScale.sample_at nameF p E m (data z R B m x)).eqTrans
    ((natScale_congr (.eqRefl _) (GaussianSineProductScaledArguments.sample_at z R B m x s)).eqTrans
      (scaleSwap.eqTrans (qmul_congr (coefficient_multiple z B m hB hm) (.eqRefl _))))

private theorem diagonal_multiple (z R B m E x p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 scaleF p (scaleData z R B m E x)) (ap2 nameF p (data z R B one x))
      ((two*R)*two) (unit p) := by
  let s := GaussianNamedNaturalScale.clock p E
  let a := clock s (two*R)
  let b := clock p (two*R)
  have h := common_late_distance (Γ := Γ) quarterF x p a b (quarter_regular x)
    (le_trans (GaussianNamedNaturalScale.clock_later p E) (bounded_clock_later s (two*R)))
    (bounded_clock_later p (two*R))
  exact distance_congr (multiple_sample_at z R B m E x p hB hm).eqSymm
    (GaussianSineProductScaledArguments.sample_at z R B one x p).eqSymm (.eqRefl _) (.eqRefl _)
    (multiply_distance (coefficient z B one) _ _ (two*R) two (unit p) (unit_positive p)
      (GaussianSineProductScaledArguments.coefficient_bound z R B one hB (le_refl one) hz) h)

theorem multiple_cross (z R B m E x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hcap : Γ ⊢[PRAAx] le m E) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent scaleF nameF (scaleData z R B m E x) (data z R B one x) := by
  apply cross_of_diagonal_rate _ _ _ _ ((two*R)*two)
    (GaussianNamedNaturalScale.name_regular nameF E m (num 4*R) (data z R B m x) (wide_input z R B m x hB hm hz) hcap)
    (name_regular z R B one x hB (le_refl one) hz)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hB.shift
  have hh : Δ ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hm.shift
  have zBound : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hz.shift
  have left : sh (scaleData z R B m E x) = scaleData (sh z) (sh R) (sh B) (sh m) (sh E) (sh x) := by
    simp only [sh,Syn.shift,subst_scaleData]
  have right : sh (data z R B one x) = data (sh z) (sh R) (sh B) one (sh x) := by
    simp only [sh,Syn.shift,GaussianSineProductScaledArguments.subst_data,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
  have cost : sh ((two*R)*two) = (two*sh R)*two := by
    simp only [sh,Syn.shift,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  change Δ ⊢[PRAAx] distanceBounded (ap2 scaleF (var 0) (sh (scaleData z R B m E x)))
    (ap2 nameF (var 0) (sh (data z R B one x))) (sh ((two*R)*two)) (unit (var 0))
  rw [left,right,cost]
  exact diagonal_multiple (sh z) (sh R) (sh B) (sh m) (sh E) (sh x) (var 0) hb hh zBound

def realRootData (k m x : PTm n) : PTm n := data (scale k oneCode) k one m x

@[simp] theorem subst_realRootData {l : ℕ} (σ : Fin n → PTm l) (k m x : PTm n) :
    Syn.subst σ (realRootData k m x) = realRootData (Syn.subst σ k) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [realRootData,oneCode]

theorem root_coefficient_rotation (k m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul imaginaryPoint (coefficient (scale k oneCode) one m) ≐
      GaussianArctangentDivisionAngles.coefficient k m := by
  let a := scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) (scale k oneCode))
  let b := scale (two*k) oneCode
  have hD := positive_product one m (le_refl one) hm
  have raw := qmul_represents imaginaryPoint (coefficient (scale k oneCode) one m) imaginaryCode a
    one (one*m) (le_refl one) hD (ofGaussian_represents _ _ (le_refl one)) (ofGaussian_represents _ _ hD)
  have rotate : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul imaginaryCode a) b := by
    dsimp only [a,b]
    apply equal_of_values <;>
      simp only [re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,imaginaryCode,
        eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) rotate (by ipra_ring) raw) (ofGaussian_represents _ _ hm)

theorem imaginary_root_sample_at (k m x p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 (imaginaryF nameF) p (realRootData k m x) ≐
      qmul (GaussianArctangentDivisionAngles.coefficient k m) (ap2 quarterF (clock p (two*k)) x) := by
  have h := GaussianSineProductScaledArguments.sample_at (Γ := Γ) (scale k oneCode) k one m x p
  exact (imaginary_at nameF p (realRootData k m x)).eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans ((qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr (root_coefficient_rotation k m hm) (.eqRefl _))))

private theorem diagonal_imaginary_root (k m x p : PTm n)
    (h : Γ ⊢[PRAAx] GaussianArctangentDivisionAngles.source k m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (imaginaryF nameF) p (realRootData k m x))
      (ap2 GaussianArctangentDivisionAngles.nameF p (GaussianArctangentDivisionAngles.data k m x)) two (unit p) := by
  let a := clock p (two*k)
  let b := GaussianArctangentDivisionAngles.clock p
  have gap := common_late_distance (Γ := Γ) quarterF x p a b (quarter_regular x)
    (bounded_clock_later p (two*k)) (bounded_clock_later p one)
  exact distance_congr (imaginary_root_sample_at k m x p h.andE₁).eqSymm
    (GaussianArctangentDivisionAngles.sample_at k m x p).eqSymm (one_mul two) (.eqRefl _)
    (multiply_distance (GaussianArctangentDivisionAngles.coefficient k m) _ _ one two (unit p) (unit_positive p)
      (GaussianArctangentDivisionAngles.coefficient_bound k m h) gap)

theorem imaginary_root_cross (k m x : PTm n) (h : Γ ⊢[PRAAx] GaussianArctangentDivisionAngles.source k m) :
    Γ ⊢[PRAAx] crossEquivalent (imaginaryF nameF) GaussianArctangentDivisionAngles.nameF
      (realRootData k m x) (GaussianArctangentDivisionAngles.data k m x) := by
  apply cross_of_diagonal_rate _ _ _ _ two
    ((imaginary_input nameF (num 4*k) (realRootData k m x)
      (wide_input (scale k oneCode) k one m x (le_refl one) h.andE₁ (natural_code_bound k))).andE₁)
    (GaussianArctangentDivisionAngles.name_regular k m x h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] GaussianArctangentDivisionAngles.source (Syn.shift k) (Syn.shift m) := by
    simpa [Fm.shift, Syn.shift, Δ] using h.shift
  simpa only [diagonalRate,Syn.shift,subst_realRootData,GaussianArctangentDivisionAngles.subst_data,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Δ] using
    diagonal_imaginary_root (Syn.shift k) (Syn.shift m) (Syn.shift x) (var 0) hs

theorem root_sine_cross (k m x N : PTm n) (h : Γ ⊢[PRAAx] GaussianArctangentDivisionAngles.source k m)
    (hR : Γ ⊢[PRAAx] input nameF N (realRootData k m x)) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (imaginaryF nameF)) (sineF GaussianArctangentDivisionAngles.nameF)
      (sineData (imaginaryF nameF) N (realRootData k m x)) (GaussianArctangentDivisionSinePositive.exactSineData k m x) :=
  sine_proper (imaginaryF nameF) GaussianArctangentDivisionAngles.nameF N two (realRootData k m x)
    (GaussianArctangentDivisionAngles.data k m x) (imaginary_input nameF N (realRootData k m x) hR)
    (GaussianArctangentDivisionAngles.exponential_input k m x h)
    (imaginary_root_cross k m x h)

theorem actual_scaled_pi_natural_multiple_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (((le one (var 3) ⋏ le one (var 2)) ⋏ le (var 2) (var 1)) ⟶
      ComplexLogarithmRemainder.bounded (var 5) (var 4*var 3) ⟶
        crossEquivalent scaleF nameF (scaleData (var 5) (var 4) (var 3) (var 2) (var 1) (var 0))
          (data (var 5) (var 4) (var 3) one (var 0))) :=
  closeUniv 6 (.impI (.impI (multiple_cross _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂ Prf.hyp1.andE₂ Prf.hyp0)))

theorem actual_real_root_sine_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianArctangentDivisionAngles.source (var 3) (var 2) ⟶ input nameF (var 0) (realRootData (var 3) (var 2) (var 1)) ⟶
      crossEquivalent (sineF (imaginaryF nameF)) (sineF GaussianArctangentDivisionAngles.nameF)
        (sineData (imaginaryF nameF) (var 0) (realRootData (var 3) (var 2) (var 1)))
          (GaussianArctangentDivisionSinePositive.exactSineData (var 3) (var 2) (var 1))) :=
  closeUniv 4 (.impI (.impI (root_sine_cross _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductScaledArgumentIdentity
