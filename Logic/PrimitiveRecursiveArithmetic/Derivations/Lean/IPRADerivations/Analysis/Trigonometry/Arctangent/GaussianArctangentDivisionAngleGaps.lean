import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentDivisionAngles
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentSlope

/-!
# Exact gaps of the original divided-angle observations

Every original half-pi observation is at least one. The divided-angle
samples share its delayed observation clock and literal denominator.
Their differences and their gaps from the endpoints follow by clearing
that positive denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleGaps

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentDivisionAngles (nameF data clock modulus odd_reserve sample_represents quarter_represents
  quarterNumerator quarterDenominator)
open GaussianArctangentExponentialPrefix (total original_mesh_source)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianRationalHorner (positive_product scalar_add_same scalar_congr scalar_rescale represents
  canonical_congr qmul_canonical)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianRootAlgebra (im_scale)
open RationalArithmetic (add)
open RationalArgmin (rationalLE)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalValueBounds (positive_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def ordinate (k m z p : PTm n) : PTm n := sndT (ap2 nameF p (data k m z))
def quarterOrdinate (p z : PTm n) : PTm n := sndT (ap2 quarterF p z)
def angleNumerator (k p : PTm n) : PTm n := two*k*quarterNumerator (clock p)
def angleDenominator (m p : PTm n) : PTm n := m*quarterDenominator (clock p)

theorem quarter_lower (p : PTm n) :
    Γ ⊢[PRAAx] le (quarterDenominator p) (quarterNumerator p) := by
  let M := meshAt p
  let L := clearing p
  have hs := original_mesh_source (Γ := Γ) p
  have endIndex : Γ ⊢[PRAAx] zero+M ≐ M := zero_add _
  have endTotal : Γ ⊢[PRAAx] total (zero+M) M L ≐ total M M L :=
    congrAp2 (sumF BaselQuadrature.Qb) endIndex (.eqRefl _)
  have low := (GaussianArctangentSlope.finite_slope zero M M L hs (le_congr endIndex.eqSymm (.eqRefl _) (le_refl M))).andE₁
  have budget : Γ ⊢[PRAAx] le (M*fact L) (M*(two*total M M L)) :=
    le_congr (.eqRefl _) ((congrMul (.eqRefl _) endTotal).eqTrans (by ipra_ring))
      (le_trans (le_add_right (M*fact L) _) low)
  exact positive_cancel hs.andE₁ budget

private theorem coordinate_represents {q N D : PTm n} (h : Γ ⊢[PRAAx] represents q (scale N imaginaryCode) D) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT q) (ZT.ofNat N) D := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) h.andE₂
  apply ZT.derive
  simp only [im_scale, imaginaryCode, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem angle_ordinate_represents (k m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (ordinate k m z p) (ZT.ofNat (angleNumerator k p)) (angleDenominator m p) :=
  coordinate_represents (sample_represents k m z p hm)

theorem quarter_ordinate_represents (p z : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (quarterOrdinate p z) (ZT.ofNat (quarterNumerator p)) (quarterDenominator p) :=
  coordinate_represents (quarter_represents p z)

private theorem denominator_positive (m p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (angleDenominator m p) :=
  positive_product _ _ hm (GaussianRationalPolynomialExponential.factorial_positive _)

private theorem add_nat_rep {a b A B D : PTm n} (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a (ZT.ofNat A) D)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b (ZT.ofNat B) D) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (add a b) (ZT.ofNat (A+B)) D := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (scalar_add_same _ _ _ _ _ hD ha hb)
  apply ZT.derive
  simp [ZT.toZ_add, ZT.toZ_ofNat,Q.mk_add,map_add]

private theorem same_den_order {a b A B D : PTm n} (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a (ZT.ofNat A) D)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b (ZT.ofNat B) D)
    (h : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] rationalLE a b :=
  comparison_of_cleared _ _ _ _ _ _ hD hD ha hb
    (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl D) h))

private theorem fraction_on_angle_denominator (A m p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fraction A m) (ZT.ofNat (A*quarterDenominator (clock p)))
      (angleDenominator m p) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (scalar_rescale _ _ _ (quarterDenominator (clock p)) (fraction_represents A m hm))
  apply ZT.derive
  simp [ZT.toZ_mul, ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem positive_at (k m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] rationalLE (fraction (two*k) m) (ordinate k m z p) :=
  same_den_order (denominator_positive m p hm) (fraction_on_angle_denominator _ _ _ hm)
    (angle_ordinate_represents k m z p hm) (le_mul_mono (le_refl (two*k)) (quarter_lower (clock p)))

theorem gap_at (k l j m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hkl : Γ ⊢[PRAAx] le (k+j) l) :
    Γ ⊢[PRAAx] rationalLE (add (ordinate k m z p) (fraction (two*j) m)) (ordinate l m z p) := by
  let Q := quarterNumerator (clock p)
  let F := quarterDenominator (clock p)
  have hD := denominator_positive m p hm
  have ha := add_nat_rep hD (angle_ordinate_represents k m z p hm) (fraction_on_angle_denominator (two*j) m p hm)
  have hF := le_mul_mono (le_refl (two*j)) (quarter_lower (Γ := Γ) (clock p))
  have order : Γ ⊢[PRAAx] le (angleNumerator k p+two*j*F) (angleNumerator l p) :=
    le_trans (add_le_add₂ (le_refl (angleNumerator k p)) hF)
      (le_congr (by dsimp only [angleNumerator,Q]; ipra_ring) (by dsimp only [angleNumerator,Q]; ipra_ring)
        (le_mul_mono (le_refl (two*Q)) hkl))
  exact same_den_order hD ha (angle_ordinate_represents l m z p hm) order

theorem top_margin_at (k J z p : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] rationalLE (add (ordinate k (modulus J) z p) (fraction one (modulus J))) (quarterOrdinate (clock p) z) := by
  let m := modulus J
  let Q := quarterNumerator (clock p)
  let F := quarterDenominator (clock p)
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hD := denominator_positive m p hm
  have ha := add_nat_rep hD (angle_ordinate_represents k m z p hm) (fraction_on_angle_denominator one m p hm)
  have hb : Γ ⊢[PRAAx] RationalArithmetic.represents (quarterOrdinate (clock p) z) (ZT.ofNat (Q*m)) (angleDenominator m p) := by
    apply scalar_congr (.eqRefl _) ?_ (mul_comm _ _) (scalar_rescale _ _ _ m (quarter_ordinate_represents (Γ := Γ) (clock p) z))
    apply ZT.derive
    simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul,Q]
  have gap : Γ ⊢[PRAAx] le (angleNumerator k p+one*F) (Q*m) :=
    le_trans (add_le_add₂ (le_refl (angleNumerator k p)) (le_mul_mono (le_refl one) (quarter_lower (clock p))))
      (le_congr (by dsimp only [angleNumerator,Q]; ipra_ring) (by ipra_ring)
        (le_mul_mono (le_refl Q) (odd_reserve k J hk)))
  exact same_den_order hD ha hb gap

theorem exact_gap_at (k l m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] add (ordinate k m z p)
        (fraction (angleNumerator (monus l k) p) (angleDenominator m p)) ≐ ordinate l m z p := by
  let D := angleDenominator m p
  let e := monus l k
  have hD := denominator_positive m p hm
  have ha := add_nat_rep hD (angle_ordinate_represents k m z p hm) (fraction_represents (angleNumerator e p) D hD)
  have hb := angle_ordinate_represents l m z p hm
  have hcan := canonical_congr (GaussianArctangentDivisionAngles.sample_at (Γ := Γ) l m z p) (qmul_canonical _ _)
  apply RationalFiniteSum.canonical_equal _ _ _ _ D D (RationalArithmetic.add_guard _ _) hcan.andE₂.andE₂ ha hb hD hD
  apply ZT.derive
  have hk := natEq (eq_add_of_le hkl)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  dsimp only [angleNumerator, e]
  ipra_simps
  linear_combination -(2*𝔞 (quarterNumerator (clock p))*𝔞 D)*hk

theorem actual_division_angle_exact_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le (var 0) (var 1) ⟶
      add (ordinate (var 0) (var 2) (var 3) (var 4))
        (fraction (angleNumerator (monus (var 1) (var 0)) (var 4)) (angleDenominator (var 2) (var 4))) ≐
      ordinate (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (exact_gap_at _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_odd_division_angle_upper_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶
      rationalLE (add (ordinate (var 0) (modulus (var 1)) (var 2) (var 3)) (fraction one (modulus (var 1))))
        (quarterOrdinate (clock (var 3)) (var 2))) :=
  closeUniv 4 (.impI (top_margin_at _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleGaps
