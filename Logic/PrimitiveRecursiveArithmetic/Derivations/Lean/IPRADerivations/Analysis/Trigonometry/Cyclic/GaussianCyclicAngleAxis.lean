import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialRoots
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngles

/-!
# Exact imaginary-axis observations for the cyclic angles

Each cyclic angle is a real rational multiple of the actual full
turn. Its stored real coordinate vanishes at every observation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicAngleAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicExponentialRoots (coefficient angleF angleData angle_at)
open GaussianArctangentQuarterExponential (quarterF radius)
open GaussianArctangentExponentialPeriod (twiceF twiceData fullTurnF fullTurnData)
open GaussianArctangentDivisionAngles (quarterNumerator quarterDenominator quarter_represents)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianBoundedConstantProductName (clock)
open GaussianExponentialReference (add_sample)
open GaussianFastValueCut (exponent)
open GaussianImaginaryNameConjugation (imaginarySamples)
open GaussianRationalHorner (represents represents_congr ofGaussian_represents qadd_represents qmul_represents
  qmul_canonical canonical_congr scalar_congr positive_product)
open GaussianRationalNaturalScale (natural_product_value)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale)
open ComplexLogarithmRemainder (scale oneCode add mul re eval_re_code)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem scale_add (a b : PTm n) :
    Γ ⊢[PRAAx] equal (add (scale a imaginaryCode) (scale b imaginaryCode)) (scale (a+b) imaginaryCode) := by
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale] <;> (try ipra_simps) <;> ring

private theorem same_scale {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] equal (scale a imaginaryCode) (scale b imaginaryCode) := by
  apply equal_of_values <;> simp only [re_scale,im_scale] <;> rw [natEq h]

private theorem quarter_positive (p : PTm n) : Γ ⊢[PRAAx] le one (quarterDenominator p) :=
  GaussianRationalPolynomialExponential.factorial_positive _

private theorem doubled_represents (p x : PTm n) :
    Γ ⊢[PRAAx] represents (ap2 twiceF p (twiceData x))
      (scale (two*quarterNumerator (exponent two p)) imaginaryCode) (quarterDenominator (exponent two p)) := by
  let t := exponent two p
  have q := quarter_represents (Γ := Γ) t x
  have h := qadd_represents _ _ _ _ _ (quarter_positive t) q q
  exact represents_congr (add_sample quarterF quarterF x x p).eqSymm
    (GaussianRootAlgebra.equal_trans (scale_add _ _) (same_scale (by ipra_ring))) (.eqRefl _) h

private theorem full_turn_represents (p x : PTm n) :
    Γ ⊢[PRAAx] represents (ap2 fullTurnF p (fullTurnData x))
      (scale (num 4*quarterNumerator (exponent two (exponent two p))) imaginaryCode)
      (quarterDenominator (exponent two (exponent two p))) := by
  let t := exponent two (exponent two p)
  have q := doubled_represents (Γ := Γ) (exponent two p) x
  have h := qadd_represents _ _ _ _ _ (quarter_positive t) q q
  exact represents_congr (add_sample twiceF twiceF (twiceData x) (twiceData x) p).eqSymm
    (GaussianRootAlgebra.equal_trans (scale_add _ _) (same_scale (by ipra_ring))) (.eqRefl _) h

theorem axis_at (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] fstT (ap2 angleF p (angleData r m x)) ≐ scalarZero := by
  let t := clock p one
  let w := exponent two (exponent two t)
  let E := quarterDenominator w
  let B := num 4*quarterNumerator w
  let a := ap2 angleF p (angleData r m x)
  let g := scale (r*B) imaginaryCode
  have hE := quarter_positive (Γ := Γ) w
  have hD := positive_product _ _ hm hE
  have b := full_turn_represents (Γ := Γ) t x
  have e : Γ ⊢[PRAAx] equal (mul (scale r oneCode) (scale B imaginaryCode)) g :=
    GaussianRootAlgebra.equal_trans (natural_product_value r (scale B imaginaryCode))
      (by dsimp only [g]; apply equal_of_values <;> simp only [re_scale,im_scale] <;> (try ipra_simps) <;> ring)
  have rprod := qmul_represents (coefficient r m) _ _ _ m E hm hE (ofGaussian_represents _ _ hm) b
  have hr : Γ ⊢[PRAAx] represents a g (m*E) := represents_congr (angle_at p r m x).eqSymm e (.eqRefl _) rprod
  have hc := canonical_congr (angle_at (Γ := Γ) p r m x) (qmul_canonical _ _)
  have zr : Γ ⊢[PRAAx] ZT.eq (re g) (ZT.ofNat zero) := by
    apply ZT.derive
    simp [g,re_scale,imaginaryCode,eval_re_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ one hc.andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (scalar_congr (.eqRefl _) zr (.eqRefl _) hr.andE₁) (scalar_zero_represents one) hD (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]

theorem imaginary_samples (r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] imaginarySamples angleF (angleData r m x) := by
  refine .allI ?_
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  simpa only [imaginarySamples,Syn.shift,GaussianCyclicExponentialRoots.subst_angleData] using
    axis_at (var 0) (Syn.shift r) (Syn.shift m) (Syn.shift x) hm'

theorem actual_cyclic_angle_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ imaginarySamples angleF (angleData (var 2) (var 1) (var 0))) :=
  closeUniv 3 (.impI (imaginary_samples _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCyclicAngleAxis
