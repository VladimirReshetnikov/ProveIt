import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasQuotientJet
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperEndpointInverse

/-! Read back an actual adjacent quotient-jet rate as the scaled difference of original
observations. The supplied observation clock depends on the grid denominator and precision. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasAdjacentObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Common
open ComplexLogarithmRemainder (oneCode normSq_one code eval_re_code eval_im_code)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRootAlgebra (equal equal_of_values normSq_equal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "raw" => GaussianNamedDifferenceQuotient.raw
local notation "inv" => GaussianNamedDifferenceQuotient.inverse

def clock (B p : PTm n) : PTm n := exponent (num 3+two*B) p

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (B p : PTm n) :
    Syn.subst σ (clock B p) = clock (Syn.subst σ B) (Syn.subst σ p) := by
  simp [clock,two,one]

theorem successor_step (A : PTm n) : Γ ⊢[PRAAx] equal (step A (succ A)) oneCode := by
  apply equal_of_values <;> simp only [step,oneCode,eval_re_code,eval_im_code,ZT.toZ_ofNat,ZT.toZ_sub]
  ipra_simps
  ring

theorem scaled_at (f : PR 2) (p x y A B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] raw f f p p x y (step A (succ A)) B ≐ natScale B (qsub (ap2 f p x) (ap2 f p y)) := by
  let h := step A (succ A)
  let z := ofGaussian h B
  let W := naturalPoint B
  have c := successor_step (Γ := Γ) A
  have e : Γ ⊢[PRAAx] z ≐ ofGaussian oneCode B := GaussianGammaFiniteValueProperness.fraction_equal _ _ B hb c
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq h ≐ one := (normSq_equal c).eqTrans normSq_one
  have hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B :=
    .andI hb (le_congr (.eqRefl _) norm.eqSymm (le_refl one))
  have a := (qmul_commutative z (inv h B)).eqTrans (GaussianNamedDifferenceQuotient.actual_inverse h B hs)
  have b := (qmul_congr e (.eqRefl W)).eqTrans
    ((qmul_commutative (ofGaussian oneCode B) W).eqTrans
      (GaussianBetaUpperEndpointInverse.natural_reciprocal_one B hb))
  have ie := GaussianEulerBetaProductPascal.inverse_unique z (inv h B) W
    (GaussianRationalReciprocal.reciprocal_canonical _) (ofGaussian_canonical _ _ (le_refl one)) a b
  exact (qmul_congr ie (.eqRefl _)).eqTrans (natScale_as_product _ _).eqSymm

theorem readback (f g : PR 2) (x y z A B p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y) (hb : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] independentRate (Q f f) g (qd f f x y (step A (succ A)) B) z two (unit p)) :
    let s := clock B p
    Γ ⊢[PRAAx] distanceBounded (natScale B (qsub (ap2 f s x) (ap2 f s y))) (ap2 g s z) (num 3) (unit p) := by
  let h₀ := step A (succ A)
  let s := clock B p
  let u := ap2 (Q f f) s (qd f f x y h₀ B)
  let v := raw f f s s x y h₀ B
  let w := ap2 g s z
  let U := unit p
  let V := unit s
  let M := num 3+two*B
  let N := GaussianNamedDifferenceQuotient.numerator B s s s
  let D := GaussianNamedDifferenceQuotient.denominator s s s
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hV : Γ ⊢[PRAAx] le one V := unit_positive s
  have hE := positive_product U V hU hV
  have hd := GaussianNamedDifferenceQuotient.denominator_positive (Γ := Γ) s s s
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq h₀ ≐ one :=
    (normSq_equal (successor_step A)).eqTrans normSq_one
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h₀ B :=
    .andI hb (le_congr (.eqRefl _) norm.eqSymm (le_refl one))
  have obs := GaussianNamedDifferenceQuotient.independent_readback f f s s s x y h₀ B (.andI hx (.andI hy sep))
  have fit : Γ ⊢[PRAAx] le (N*(U*V)) (((one+two*B)*U)*D) := le_of_eq_add (d := zero) (by
    dsimp only [N,D,GaussianNamedDifferenceQuotient.numerator,GaussianNamedDifferenceQuotient.denominator,V]
    ipra_ring)
  have left : Γ ⊢[PRAAx] distanceBounded v u ((one+two*B)*U) (U*V) :=
    distance_symmetric _ _ _ _ hE (distance_radius_mono _ _ _ _ _ _ hd hE fit obs)
  have right : Γ ⊢[PRAAx] distanceBounded u w (two*V+two*U) (U*V) :=
    diagonal_rate (Q f f) g (qd f f x y h₀ B) z two U s hU h
  have both : Γ ⊢[PRAAx] distanceBounded v w (two*V+M*U) (U*V) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [M]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hE left right)
  have pay : Γ ⊢[PRAAx] le (M*U) V := query_budget M p
  have last : Γ ⊢[PRAAx] le ((two*V+M*U)*U) (num 3*(U*V)) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right U (add_le_add (le_refl (two*V)) pay))
  exact distance_congr (scaled_at f s x y A B hb) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hE hU last both)

theorem dyadic_readback (f g : PR 2) (x y z A B p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y) (hb : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] independentRate (Q f f) g (qd f f x y (step A (succ A)) B) z two (unit (p+two))) :
    let s := clock B (p+two)
    Γ ⊢[PRAAx] distanceBounded (natScale B (qsub (ap2 f s x) (ap2 f s y))) (ap2 g s z) one (unit p) := by
  have pow : Γ ⊢[PRAAx] unit (p+two) ≐ num 4*unit p :=
    (pw_add two p two).eqTrans
      ((congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _)))).eqTrans (by unfold unit; ipra_ring))
  have fit : Γ ⊢[PRAAx] le (num 3*unit p) (one*unit (p+two)) :=
    le_congr (.eqRefl _) ((one_mul _).eqTrans pow).eqSymm
      (le_of_eq_add (d := unit p) (by ipra_ring))
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p) fit
    (readback f g x y z A B (p+two) hx hy hb h)

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasAdjacentObservation
