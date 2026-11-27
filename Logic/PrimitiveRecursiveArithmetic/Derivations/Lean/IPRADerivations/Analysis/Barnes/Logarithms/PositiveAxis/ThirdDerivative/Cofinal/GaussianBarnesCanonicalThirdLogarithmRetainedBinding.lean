import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.Cofinal.GaussianBarnesCanonicalThirdLogarithmCofinal
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# The full cubic Barnes logarithm series and the original retained evaluator

The full positive-axis series equals the sum of the exact kept cubic rows
and the previously checked order-three retained logarithmic derivative
name. Both sides use the original rational row program and its factorial
normalization.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmRetainedBinding

open_ipra
open LeanProofs.IPRA.Common (mul_le_mul pos_of_one_le pw_two)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdLogarithmSeries (value)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "T" => GaussianBarnesCanonicalHigherDerivative.nameF
local notation "S" => GaussianBarnesCanonicalThirdLogarithmCofinal.nameF
local notation "Sdata" => GaussianBarnesCanonicalThirdLogarithmCofinal.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

def data (A B R : PTm n) : PTm n :=
  addData (value A B (initial R)) (GaussianBarnesCanonicalHigherDerivative.data (center A B) R B zero)

def nameF : PR 2 := addF constantF T

def suffixLength (p : PTm n) : PTm n :=
  GaussianBarnesCanonicalHigherCofinal.length (GaussianBarnesCanonicalHigherDerivative.clock p zero) zero

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (data A B R) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by
  simp [data]

theorem split_at (p A B R : PTm n) : Γ ⊢[PRAAx]
    qadd (ap2 constantF p (value A B (initial R)))
      (ap2 T p (GaussianBarnesCanonicalHigherDerivative.data (center A B) R B zero)) ≐
      value A B (initial R+suffixLength p) := by
  let N := pred (initial R)
  have h : Γ ⊢[PRAAx] succ N ≐ initial R := (pos_of_one_le (initial_positive R)).eqSymm
  let L := suffixLength p
  let z := center A B
  have kept : Γ ⊢[PRAAx] value A B (succ N) ≐ value A B (initial R) :=
    GaussianRationalFiniteSum.sum_index_congr GaussianBarnesCanonicalHigherDerivative.body h (.eqRefl _)
  have tail : Γ ⊢[PRAAx] GaussianBarnesCanonicalThirdLogarithmTail.value A B N L ≐
      GaussianBarnesCanonicalHigherDerivative.value z B (initial R) zero L := by
    change Γ ⊢[PRAAx] GaussianBarnesCanonicalHigherDerivative.value z B (succ N) zero L ≐
      GaussianBarnesCanonicalHigherDerivative.value z B (initial R) zero L
    ipra_congr (GaussianBarnesCanonicalHigherDerivative.value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      with [.eqRefl _,.eqRefl _,h,.eqRefl _,.eqRefl _]
  have full : Γ ⊢[PRAAx] value A B (succ N+L) ≐ value A B (initial R+L) :=
    GaussianRationalFiniteSum.sum_index_congr GaussianBarnesCanonicalHigherDerivative.body (congrAdd h (.eqRefl _)) (.eqRefl _)
  exact (qadd_congr (constant_at _ _) (GaussianBarnesCanonicalHigherDerivative.sample_at p z R B zero)).eqTrans
    ((qadd_congr kept tail).eqSymm.eqTrans
      ((GaussianBarnesCanonicalThirdLogarithmCauchy.split A B N L).eqSymm.eqTrans full))

theorem length_lower (p : PTm n) : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalThirdLogarithmCofinal.cutoff p)
    (suffixLength p) := by
  let g : PTm n := GaussianBarnesCanonicalThirdLogarithmCauchy.gain
  let C : PTm n := GaussianBarnesCanonicalHigherRows.coefficientGain zero
  let v := GaussianBarnesCanonicalHigherDerivative.clock p zero
  have hC : Γ ⊢[PRAAx] g*two ≐ C :=
    ((pw_succ two two).eqTrans (congrMul (pw_two two) (.eqRefl _))).eqSymm
  have hg : Γ ⊢[PRAAx] le g C :=
    le_congr (by ipra_ring) hC (mul_le_mul (le_refl g) (le_succ_self one))
  have clock : Γ ⊢[PRAAx] le p v := le_add_right _ _
  exact mul_le_mul hg (GaussianExponentialReference.unit_monotone clock)

theorem diagonal_at (p A B R : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 S p (Sdata A B)) (ap2 nameF p (data A B R)) (num 4) (unit p) := by
  let z := center A B
  let N := pred (initial R)
  let L := suffixLength p
  let c := value A B (initial R+L)
  have late := GaussianBarnesCanonicalThirdLogarithmCofinal.late_prefix_error p A B (N+L)
    (.andI hA h.andE₁) (le_trans (length_lower p) (le_add_left L N))
  have ct : Γ ⊢[PRAAx] value A B (succ (N+L)) ≐ c :=
    GaussianRationalFiniteSum.sum_index_congr GaussianBarnesCanonicalHigherDerivative.body
      ((by ipra_ring : Γ ⊢[PRAAx] succ (N+L) ≐ succ N+L).eqTrans
        (congrAdd (pos_of_one_le (initial_positive R)).eqSymm (.eqRefl _))) (.eqRefl _)
  have left := distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr ct (.eqRefl _) (.eqRefl _) (.eqRefl _) late)
  have add := GaussianNameRingLaws.add_sample_error constantF T (value A B (initial R))
    (GaussianBarnesCanonicalHigherDerivative.data z R B zero) p
    (constant_regular _) (GaussianBarnesCanonicalHigherDerivative.regular z R B zero h)
  have right : Γ ⊢[PRAAx] distanceBounded c (ap2 nameF p (data A B R)) (num 3) (unit p) :=
    distance_symmetric _ _ _ _ (unit_positive p)
      (distance_congr (.eqRefl _) (split_at p A B R) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) add)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) left right)

theorem binding (A B R : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] crossEquivalent S nameF (Sdata A B) (data A B R) := by
  have reg : Γ ⊢[PRAAx] pointCN nameF (data A B R) := add_fast _ _ _ _
    (constant_regular _) (GaussianBarnesCanonicalHigherDerivative.regular _ _ _ _ h)
  apply cross_of_diagonal_rate _ _ _ _ (num 4) (GaussianBarnesCanonicalThirdLogarithmCofinal.regular _ _ (.andI hA h.andE₁)) reg
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let r := Syn.shift R
  have ha : Γ.map Fm.shift ⊢[PRAAx] le one a := by simpa [Fm.shift,Syn.shift,a,one] using hA.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] disk (center a b) r b := by
    simpa only [Fm.shift,Syn.shift,a,b,r,GaussianBarnesCanonicalLogCofinal.subst_source,
      GaussianBarnesCanonicalThirdLogarithmRows.subst_center] using h.shift
  simpa only [diagonalRate,Syn.shift,a,b,r,subst_data,GaussianBarnesCanonicalThirdLogarithmCofinal.subst_data,
    LeanProofs.IPRA.PTm.subst_num] using diagonal_at (var 0) a b r ha hd

theorem actual_Barnes_cubic_logarithm_retained_binding_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let A := var 0
       let B := var 1
       let R := var 2
       (le one A ⋏ disk (center A B) R B) ⟶ crossEquivalent S nameF (Sdata A B) (data A B R)) :=
  closeUniv 3 (.impI (binding _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmRetainedBinding
