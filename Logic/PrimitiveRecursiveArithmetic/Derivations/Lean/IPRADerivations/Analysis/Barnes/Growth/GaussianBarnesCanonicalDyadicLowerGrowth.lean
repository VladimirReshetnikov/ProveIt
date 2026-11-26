import IPRADerivations.Analysis.Barnes.Growth.BarnesIntegerGrowth
import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerValues
import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.GaussianBarnesCanonicalIntegerSampleLower

/-!
# Dyadic lower witnesses for the original Barnes function

The integer argument of the canonical sampler is shifted by one.
At each dyadic scale, the exact superfactorial value provides a lower
witness inside the corresponding disk for (G). A primitive-recursive
choice of the scale gives arbitrarily large quadratic type thresholds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicLowerGrowth

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open BarnesInteger (barnes)
open ComplexLogarithmRemainder (normSq oneCode scale)
open GaussianBarnesCanonicalIntegerSampleLower (sample sample_lower)
open GaussianBarnesCanonicalIntegerValues (integerValue original_integer_value)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

def centerIndex (j : PTm n) : PTm n := num 4*unit j
def diskRadius (j : PTm n) : PTm n := unit (j+num 3)
def lowerExponent (j : PTm n) : PTm n := succ j*(unit j*unit j)

theorem radius_readback (j : PTm n) : Γ ⊢[PRAAx] diskRadius j ≐ num 8*unit j := by
  have eight : Γ ⊢[PRAAx] pw two (num 3) ≐ num 8 :=
    (pw_succ two (num 2)).eqTrans
      ((congrMul ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))) (.eqRefl _)).eqTrans (by ipra_ring))
  exact (pw_add two j (num 3)).eqTrans ((congrMul (.eqRefl _) eight).eqTrans (mul_comm _ _))

theorem inside_disk (j : PTm n) : Γ ⊢[PRAAx] le (succ (centerIndex j)) (diskRadius j) := by
  let m := unit j
  let i := centerIndex j
  have first := le_congr (succ_eq_add_one (Γ := Γ) i).eqSymm (.eqRefl (i+m))
    (add_le_add₂ (le_refl i) (unit_positive j))
  exact le_trans first (le_congr (.eqRefl _) (radius_readback j).eqSymm
    (le_of_eq_add (d := num 3*m) (by dsimp [i,centerIndex]; ipra_ring)))

theorem integer_bound (j : PTm n) : Γ ⊢[PRAAx] le (unit (lowerExponent j)) (barnes (centerIndex j)) := by
  let m := unit j
  have twice : Γ ⊢[PRAAx] two*m ≐ unit (succ j) :=
    ((pw_succ two j).eqTrans (mul_comm _ _)).eqSymm
  have e := (congrAp2 powF (.eqRefl (m*m)) twice).eqTrans (pw_mul two (succ j) (m*m))
  exact le_congr e (.eqRefl _) (BarnesIntegerGrowth.tiled_lower m (unit_positive j))

def valueIdentity (j : PTm n) : Fm PTm n :=
  let i := centerIndex j
  crossEquivalent V constantF (vd (scale i oneCode) i one) (integerValue i)

theorem dyadic_witness (j : PTm n) : Γ ⊢[PRAAx]
    (le (succ (centerIndex j)) (diskRadius j) ⋏
      le (unit (lowerExponent j)) (barnes (centerIndex j))) ⋏ valueIdentity j :=
  .andI (.andI (inside_disk j) (integer_bound j)) (original_integer_value (centerIndex j))

def typeClock (T : PTm n) : PTm n := num 128*succ T

def typeExponent (T j : PTm n) : PTm n := (two*succ T)*(diskRadius j*diskRadius j)

theorem type_exponent_margin (T : PTm n) : Γ ⊢[PRAAx]
    le (succ (typeExponent T (typeClock T))) (lowerExponent (typeClock T)) := by
  let j := typeClock T
  let m := unit j
  have e : Γ ⊢[PRAAx] typeExponent T j ≐ j*(m*m) := by
    have r := radius_readback (Γ := Γ) j
    refine (congrMul (.eqRefl (two*succ T)) (congrMul r r)).eqTrans ?_
    dsimp [j,m,typeClock]
    ipra_ring
  have left := (succ_eq_add_one (typeExponent T j)).eqTrans (congrAdd e (.eqRefl one))
  have hm := positive_product _ _ (unit_positive (Γ := Γ) j) (unit_positive j)
  exact le_congr left.eqSymm (by dsimp [lowerExponent,m]; ipra_ring)
    (add_le_add₂ (le_refl (j*(m*m))) hm)

theorem type_witness (T : PTm n) :
    let j := typeClock T
    Γ ⊢[PRAAx] (le (succ (centerIndex j)) (diskRadius j) ⋏
      le (unit (typeExponent T j)) (barnes (centerIndex j))) ⋏ valueIdentity j :=
  let j := typeClock T
  .andI (.andI (inside_disk j) (le_trans (unit_monotone (le_trans (le_succ_self _) (type_exponent_margin T))) (integer_bound j)))
    (original_integer_value (centerIndex j))

theorem exponent_sample_lower (p j a : PTm n) (hp : Γ ⊢[PRAAx] le two p)
    (ha : Γ ⊢[PRAAx] le (succ a) (lowerExponent j)) : Γ ⊢[PRAAx]
    lower (sample p (centerIndex j)) (unit a) one := by
  let q := sample p (centerIndex j)
  let D := rawDen q
  let z := rawGaussian q
  let A := unit a
  have hi := le_trans (unit_monotone ha) (integer_bound j)
  have raw := sample_lower p (centerIndex j) (unit (succ a)) hp (unit_positive (succ a)) hi
  have hD := raw_den_positive (Γ := Γ) q
  have h2 := le_succ_self (Γ := Γ) one
  have h4 := positive_product _ _ h2 h2
  have old := lower_to_cleared q z D (unit (succ a)) two hD h2 (raw_represents q) raw
  have e : Γ ⊢[PRAAx] unit (succ a) ≐ unit a*two := pw_succ two a
  have expanded := le_congr (congrMul (congrMul e e) (.eqRefl _)) (.eqRefl _) old
  have fit : Γ ⊢[PRAAx] le ((two*two)*(A*A*(D*D))) ((two*two)*(one*one*normSq z)) :=
    le_congr (by dsimp [A]; ipra_ring) (by ipra_ring) expanded
  exact lower_from_representation q z D A one hD (le_refl one) (raw_represents q) (Common.mul_cancel_le h4 fit)

theorem order_margin (j : PTm n) (hj : Γ ⊢[PRAAx] le (num 64) j) : Γ ⊢[PRAAx]
    le (succ (diskRadius j*diskRadius j)) (lowerExponent j) := by
  let D := unit j*unit j
  have r := radius_readback (Γ := Γ) j
  have sq : Γ ⊢[PRAAx] diskRadius j*diskRadius j ≐ num 64*D :=
    (congrMul r r).eqTrans (by dsimp [D]; ipra_ring)
  have left := (succ_eq_add_one _).eqTrans (congrAdd sq (.eqRefl one))
  have hD := positive_product _ _ (unit_positive (Γ := Γ) j) (unit_positive j)
  exact le_congr left.eqSymm (by dsimp [lowerExponent,D]; ipra_ring)
    (add_le_add₂ (mul_le_mul_right D hj) hD)

theorem order_sample_witness (p j : PTm n) (hp : Γ ⊢[PRAAx] le two p) (hj : Γ ⊢[PRAAx] le (num 64) j) :
    Γ ⊢[PRAAx] le (succ (centerIndex j)) (diskRadius j) ⋏
      lower (sample p (centerIndex j)) (unit (diskRadius j*diskRadius j)) one :=
  .andI (inside_disk j) (exponent_sample_lower p j _ hp (order_margin j hj))

theorem type_sample_witness (p T : PTm n) (hp : Γ ⊢[PRAAx] le two p) :
    let j := typeClock T
    Γ ⊢[PRAAx] le (succ (centerIndex j)) (diskRadius j) ⋏
      lower (sample p (centerIndex j)) (unit (typeExponent T j)) one :=
  .andI (inside_disk _) (exponent_sample_lower p _ _ hp (type_exponent_margin T))

theorem actual_Barnes_dyadic_lower_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let j := var 0
     (le (succ (centerIndex j)) (diskRadius j) ⋏
       le (unit (lowerExponent j)) (barnes (centerIndex j))) ⋏ valueIdentity j) :=
  closeUniv 1 (dyadic_witness _)

theorem actual_Barnes_canonical_integer_type_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let T := var 0
     let j := typeClock T
     (le (succ (centerIndex j)) (diskRadius j) ⋏
       le (unit (typeExponent T j)) (barnes (centerIndex j))) ⋏ valueIdentity j) :=
  closeUniv 1 (type_witness _)

theorem actual_Barnes_infinite_type_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let p := var 0
     let T := var 1
     let j := typeClock T
     le two p ⟶ le (succ (centerIndex j)) (diskRadius j) ⋏
       lower (sample p (centerIndex j)) (unit (typeExponent T j)) one) :=
  closeUniv 2 (.impI (type_sample_witness _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicLowerGrowth
