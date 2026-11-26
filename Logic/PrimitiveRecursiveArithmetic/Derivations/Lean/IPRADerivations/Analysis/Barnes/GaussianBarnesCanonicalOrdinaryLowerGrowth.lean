import IPRADerivations.Analysis.Barnes.BarnesDyadicRadius
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDyadicLowerGrowth

/-!
# Lower order witnesses for ordinary Barnes radii

For every sufficiently large integer radius, compute a dyadic disk
inside it. The original integer Barnes value in that disk also pays
the square of the given radius, with one bit of margin for observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalOrdinaryLowerGrowth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BarnesDyadicRadius (bracket threshold_le_index)
open GaussianBarnesCanonicalDyadicLowerGrowth
  (centerIndex diskRadius lowerExponent radius_readback inside_disk exponent_sample_lower valueIdentity)
open GaussianBarnesCanonicalIntegerSampleLower (sample)
open GaussianBarnesCanonicalIntegerValues (original_integer_value)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalLowerBounds (lower)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def index (r : PTm n) : PTm n := monus (BarnesDyadicRadius.index r) (num 3)
def witness (r : PTm n) : PTm n := centerIndex (index r)

private theorem index_budget (r : PTm n) (hr : Γ ⊢[PRAAx] le (unit (num 259)) r) :
    Γ ⊢[PRAAx] le (num 256) (index r) ⋏ (index r+num 3 ≐ BarnesDyadicRadius.index r) := by
  let J := BarnesDyadicRadius.index r
  let j := index r
  have hJ := threshold_le_index r (num 259) (le_trans (unit_positive _) hr) hr
  have atLeastThree : Γ ⊢[PRAAx] le (num 3) J :=
    le_trans (le_of_eq_add (d := num 256) (by ipra_ring)) hJ
  have expand : Γ ⊢[PRAAx] j+num 3 ≐ J := (add_comm _ _).eqTrans (eq_add_of_le atLeastThree).eqSymm
  have full : Γ ⊢[PRAAx] J ≐ num 3+(num 256+monus J (num 259)) :=
    (eq_add_of_le hJ).eqTrans (by ipra_ring)
  have split : Γ ⊢[PRAAx] j ≐ num 256+monus J (num 259) := LeanProofs.IPRA.Common.monus_of_eq full
  exact .andI (le_congr (.eqRefl _) split.eqSymm (le_add_right _ _)) expand

theorem disk_bracket (r : PTm n) (hr : Γ ⊢[PRAAx] le (unit (num 259)) r) :
    Γ ⊢[PRAAx] le (diskRadius (index r)) r ⋏ le r (num 16*unit (index r)) := by
  let J := BarnesDyadicRadius.index r
  let j := index r
  have fit := bracket r (le_trans (unit_positive _) hr)
  have low : Γ ⊢[PRAAx] diskRadius j ≐ unit J :=
    congrAp2 powF (index_budget r hr).andE₂ (.eqRefl two)
  have high : Γ ⊢[PRAAx] unit (succ J) ≐ num 16*unit j :=
    (pw_succ two J).eqTrans ((congrMul (low.eqSymm.eqTrans (radius_readback j)) (.eqRefl two)).eqTrans (by ipra_ring))
  exact .andI (le_congr low.eqSymm (.eqRefl _) fit.andE₁)
    (le_congr (.eqRefl _) high (le_of_lt fit.andE₂))

theorem order_margin (r : PTm n) (hr : Γ ⊢[PRAAx] le (unit (num 259)) r) :
    Γ ⊢[PRAAx] le (succ (r*r)) (lowerExponent (index r)) := by
  let j := index r
  let D := unit j*unit j
  have large := (disk_bracket r hr).andE₂
  have square : Γ ⊢[PRAAx] le (r*r) (num 256*D) :=
    le_congr (.eqRefl _) (by dsimp only [D]; ipra_ring) (LeanProofs.IPRA.Common.mul_le_mul large large)
  have hj := (index_budget r hr).andE₁
  have hD := positive_product _ _ (unit_positive (Γ := Γ) j) (unit_positive j)
  have finish : Γ ⊢[PRAAx] le (succ (num 256*D)) (lowerExponent j) :=
    le_congr (succ_eq_add_one _).eqSymm (by dsimp only [lowerExponent,D]; ipra_ring)
      (add_le_add₂ (mul_le_mul_right D hj) hD)
  exact le_trans (LeanProofs.IPRA.Common.succ_le_succ square) finish

theorem order_sample_witness (p r : PTm n) (hp : Γ ⊢[PRAAx] le two p)
    (hr : Γ ⊢[PRAAx] le (unit (num 259)) r) :
    Γ ⊢[PRAAx] le (succ (witness r)) r ⋏ lower (sample p (witness r)) (unit (r*r)) one :=
  .andI (le_trans (inside_disk (index r)) (disk_bracket r hr).andE₁)
    (exponent_sample_lower p (index r) (r*r) hp (order_margin r hr))

theorem actual_Barnes_ordinary_lower_order_witness_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let p := var 0
       let r := var 1
       le two p ⟶ le (unit (num 259)) r ⟶
         (le (succ (witness r)) r ⋏ lower (sample p (witness r)) (unit (r*r)) one) ⋏ valueIdentity (index r)) :=
  closeUniv 2 (.impI (.impI (.andI (order_sample_witness _ _ Prf.hyp1 Prf.hyp0)
    (original_integer_value (witness (var 1))))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalOrdinaryLowerGrowth
