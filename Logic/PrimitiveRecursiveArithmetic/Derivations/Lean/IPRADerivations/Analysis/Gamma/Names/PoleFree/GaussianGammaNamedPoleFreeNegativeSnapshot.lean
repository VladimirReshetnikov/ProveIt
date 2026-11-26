import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreePositiveAdmission
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitCompactTimeBounds
import IPRADerivations.Core.Gcd

/-!
# A negative pole interval from a real observation

Euclidean division of the absolute real numerator by its denominator
locates the two adjacent poles. Their certified separations put the
offset within the rational window used by the negative Gamma evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeNegativeSnapshot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg)
open ComplexLogarithmRemainder (re im)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaNamedPoleFreePositiveAdmission (axis_pole_gap)
open GaussianNamedRightHalfPlane (numerator denominator threshold)
open GaussianRationalL1 (raw_den_positive)
open GaussianL1 (abs_ofNat)
open GaussianSignedNameExponentialOrder (realSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "poleSource" => GaussianGammaNamedPoleFree.source

def nonpositiveAt (f : PR 2) (k x : PTm n) : Fm PTm n :=
  zle (re (numerator f k x)) (ZT.ofNat zero)
def magnitude (f : PR 2) (k x : PTm n) : PTm n := zabs (re (numerator f k x))
def interval (f : PR 2) (k x : PTm n) : PTm n := quo (magnitude f k x) (denominator f k x)
def remainder (f : PR 2) (k x : PTm n) : PTm n := rem (magnitude f k x) (denominator f k x)
def offsetNumerator (f : PR 2) (k x : PTm n) : PTm n := monus (denominator f k x) (remainder f k x)

private theorem value_of_nonpositive (a : ZT n) (h : Γ ⊢[PRAAx] zle a (ZT.ofNat zero)) :
    ZT.toZ Γ a = -𝔞 (zabs a) := by
  let d := PolynomialBisection.slack a (ZT.ofNat zero)
  have e := zle_toZ h
  have val : ZT.toZ Γ a = ZT.toZ Γ (-(ZT.ofNat d)) := by
    simp only [d,PolynomialBisection.slack,ZT.toZ_neg,ZT.toZ_ofNat] at e ⊢
    ipra_simps
    linear_combination e
  have abs : Γ ⊢[PRAAx] zabs a ≐ d := (zabs_congr val).eqTrans ((zabs_neg _).eqTrans (abs_ofNat d))
  rw [natEq abs,val,ZT.toZ_neg,ZT.toZ_ofNat]

private theorem positive_factor (B E u : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le B (E*u)) : Γ ⊢[PRAAx] le one u := by
  refine .orE (lt_or_le zero u) Prf.hyp0 ?_
  have e : le u zero :: Γ ⊢[PRAAx] u ≐ zero := le_antisymm Prf.hyp0 (zero_le u)
  have impossible : le u zero :: Γ ⊢[PRAAx] le one zero := le_trans hB.wk (le_congr (.eqRefl _) ((congrMul (.eqRefl E) e).eqTrans (by ipra_ring)) h.wk)
  exact le_lt_absurd (le one u) impossible (show _ ⊢[PRAAx] lt zero one from le_refl one)

theorem finite_window (f : PR 2) (k x R E : PTm n)
    (h : Γ ⊢[PRAAx] poleSource f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hs : Γ ⊢[PRAAx] nonpositiveAt f k x) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source (offsetNumerator f k x) (denominator f k x) E ⋏
      (ZT.eq (re (translated (numerator f k x) (denominator f k x) (succ (interval f k x))))
        (ZT.ofNat (offsetNumerator f k x)) ⋏
       ZT.eq (im (translated (numerator f k x) (denominator f k x) (succ (interval f k x)))) (ZT.ofNat zero)) := by
  let z := numerator f k x
  let B := denominator f k x
  let J := interval f k x
  let r := remainder f k x
  let a := offsetNumerator f k x
  have hB : Γ ⊢[PRAAx] le one B := raw_den_positive _
  have native := GaussianGammaNamedPoleFree.source_at f k x R E h
  have hE := native.andE₂.andE₂.andE₁
  have split : Γ ⊢[PRAAx] (magnitude f k x ≐ B*J+r) ⋏ lt r B :=
    div_mod_at (RationalIntegerNormalization.positive_form hB)
  have remain : Γ ⊢[PRAAx] B ≐ r+a := eq_add_of_le (le_of_lt split.andE₂)
  have e := natEq split.andE₁
  have er := natEq remain
  have neg := value_of_nonpositive (re z) hs
  have im0 : ZT.toZ Γ (im z) = ZT.toZ Γ (ZT.ofNat zero) :=
    ZT.toZ_eq (GaussianNamedGammaPositiveLower.decoded_imaginary_zero f k x hr)
  have translate_im (j : PTm n) : Γ ⊢[PRAAx] ZT.eq (im (translated z B j)) (ZT.ofNat zero) := by
    apply ZT.derive
    simp only [translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,im0]
    ring
  have real_left : ZT.toZ Γ (re (translated z B J)) = ZT.toZ Γ (-(ZT.ofNat r)) := by
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
      ZT.toZ_neg,ZT.toZ_ofNat]
    change ZT.toZ Γ (re z) = -𝔞 (magnitude f k x) at neg
    ipra_simps
    linear_combination neg-e
  have real_right : ZT.toZ Γ (re (translated z B (succ J))) = ZT.toZ Γ (ZT.ofNat a) := by
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
    change ZT.toZ Γ (re z) = -𝔞 (magnitude f k x) at neg
    ipra_simps
    linear_combination neg-e+er
  have abs_left : Γ ⊢[PRAAx] zabs (re (translated z B J)) ≐ r :=
    (zabs_congr real_left).eqTrans ((zabs_neg _).eqTrans (abs_ofNat r))
  have abs_right : Γ ⊢[PRAAx] zabs (re (translated z B (succ J))) ≐ a :=
    (zabs_congr real_right).eqTrans (abs_ofNat a)
  have left := axis_pole_gap z B E J (translate_im J) (GaussianGammaNamedPoleFreeProperness.every_pole_at z R B E J native)
  have right := axis_pole_gap z B E (succ J) (translate_im (succ J))
    (GaussianGammaNamedPoleFreeProperness.every_pole_at z R B E (succ J) native)
  have rb := le_congr (.eqRefl _) (congrMul (.eqRefl _) abs_left) left
  have ab := le_congr (.eqRefl _) (congrMul (.eqRefl _) abs_right) right
  have cap : Γ ⊢[PRAAx] le (E*a+B) (E*B) :=
    le_congr (add_comm _ _) ((by ipra_ring : Γ ⊢[PRAAx] E*r+E*a ≐ E*(r+a)).eqTrans
      (congrMul (.eqRefl E) remain.eqSymm)) (add_le_add_right (E*a) rb)
  have inside : Γ ⊢[PRAAx] lt a B :=
    le_congr ((add_comm one a).eqTrans (succ_eq_add_one a).eqSymm) remain.eqSymm (add_le_add_right a (positive_factor B E r hB rb))
  exact .andI (.andI (.andI (positive_factor B E a hB ab) inside) (.andI hE (.andI ab cap)))
    (.andI (ZT.derive real_right) (translate_im (succ J)))

theorem actual_pole_free_negative_snapshot_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((poleSource f (var 0) (var 1) (var 2) ⋏ (realSamples f (var 0) ⋏ nonpositiveAt f (threshold (var 2)) (var 0))) ⟶
        GaussianEulerUnitCompactTimeBounds.source (offsetNumerator f (threshold (var 2)) (var 0))
          (denominator f (threshold (var 2)) (var 0)) (var 2)) :=
  closeUniv 3 (.impI ((finite_window f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂).andE₁))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeNegativeSnapshot
