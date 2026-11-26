/-
Exact quadratic expansion of the original Barnes prefactor and the kept
finite correction exponent. Both are polynomial in the native step.
-/
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalRelativeLogIncrement
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSquareCancellation

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeExponentTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf square squareStep twicePoint linearSquare incrementData)
open GaussianBarnesCanonicalRelativeLogIncrement (exponentData prefactorF prefactorData correctionF correctionData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_commutative)
open GaussianRationalHorner (ofGaussian qadd qmul)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "inc_add" => GaussianBarnesCanonicalPrefactorExponentDerivative.increment_add
local notation "regular" => GaussianBarnesCanonicalPrefactorExponentDerivative.regular

def prefactorQuadratic (z h B : PTm n) : PTm n :=
  exponentOf (ofGaussian h B) (qadd (linearSquare z h B) (square h B))

def correctionQuadratic (z h B N : PTm n) : PTm n :=
  qadd (GaussianBarnesCanonicalHeadCorrectionDerivative.linear z h B N)
    (GaussianBarnesCanonicalHeadCorrectionDerivative.remainder h B N)

@[simp] theorem subst_prefactorQuadratic {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (prefactorQuadratic z h B) = prefactorQuadratic (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) := by
  simp [prefactorQuadratic]

@[simp] theorem subst_correctionQuadratic {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (correctionQuadratic z h B N) =
      correctionQuadratic (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [correctionQuadratic]

theorem square_expansion (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    squareStep z h B ≐ qadd (linearSquare z h B) (square h B) := by
  let x := ofGaussian z B
  let d := ofGaussian h B
  let y := ofGaussian (add z h) B
  have diff := GaussianBarnesCanonicalHeadCorrectionDerivative.point_increment z h B hB
  have xy : Γ ⊢[PRAAx] qadd x d ≐ y :=
    (qadd_congr (.eqRefl _) diff.eqSymm).eqTrans
      (GaussianRationalLinearProduct.add_sub_right x y (GaussianRationalHorner.ofGaussian_canonical _ _ hB))
  have sum : Γ ⊢[PRAAx] qadd y x ≐ qadd (qadd x x) d :=
    (qadd_congr xy.eqSymm (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative (qadd x d) x).eqTrans
        (GaussianRationalSumAlgebra.qadd_associative x x d).eqSymm)
  exact (GaussianRationalSquareCancellation.difference_factorization y x).eqTrans
    ((qmul_congr diff sum).eqTrans (GaussianRationalCoefficientScaling.qmul_add d (qadd x x) d))

private theorem prefactor_difference (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent prefactorF E (prefactorData z h B) (incrementData z h B) := by
  let w := add z h
  let x := exponentData z B
  let y := exponentData w B
  let t := incrementData z h B
  let s := addData t x
  let M := addF E E
  let N := negativeF E
  let u := negativeData x
  have hx : Γ ⊢[PRAAx] pointCN E x := regular _ _
  have hy : Γ ⊢[PRAAx] pointCN E y := regular _ _
  have ht : Γ ⊢[PRAAx] pointCN E t := regular _ _
  have hu := negative_fast E x hx
  have hsum : Γ ⊢[PRAAx] crossEquivalent M E s y :=
    cross_trans M M E s (addData x t) y (add_commutative E E t x ht hx) (inc_add z h B hB)
  have lift := GaussianNamedGammaHalfShift.add_cross E M N N y s u u hy (add_fast _ _ _ _ ht hx) hu hu
    (cross_symm _ _ _ _ hsum) (cross_refl _ _ hu)
  exact cross_trans (D E E) (D M E) E (dd y x) (dd s x) t lift
    (GaussianNamedStrictOrderDifference.sum_sub_right E E t x ht hx)

theorem prefactor_cross (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent prefactorF E (prefactorData z h B) (prefactorQuadratic z h B) := by
  let x := incrementData z h B
  let y := prefactorQuadratic z h B
  have e : Γ ⊢[PRAAx] x ≐ y := by
    ipra_congr (exponentOf (var 0) (var 1) : PTm 2) with
      [.eqRefl (ofGaussian h B), square_expansion z h B hB] using [x,y,incrementData,prefactorQuadratic]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr prefactorF E _ _ _ _ (.eqRefl _) e
    (prefactor_difference z h B hB)

private theorem constant_difference (a b c : PTm n) (hc : Γ ⊢[PRAAx] qsub a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (D constantF constantF) constantF (dd a b) c := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  have eq : Δ ⊢[PRAAx] qsub (sh a) (sh b) ≐ sh c := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift
  have read := (qsub_congr (constant_at p (sh a)) (constant_at p (sh b))).eqTrans
    (eq.eqTrans (constant_at p (sh c)).eqSymm)
  simpa only [Δ,sh,p,Syn.shift,GaussianNamedDifference.subst_data,PTm.subst_num] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifference.sample_error constantF constantF (sh a) (sh b) p (constant_regular _) (constant_regular _))

theorem correction_cross (z h B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent correctionF constantF (correctionData z h B N) (correctionQuadratic z h B N) :=
  constant_difference _ _ _ (GaussianBarnesCanonicalHeadCorrectionDerivative.exact_expansion z h B N hB)

theorem actual_Barnes_prefactor_quadratic_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ crossEquivalent prefactorF E (prefactorData (var 0) (var 1) (var 2))
      (prefactorQuadratic (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (prefactor_cross _ _ _ Prf.hyp0))

theorem actual_Barnes_kept_correction_quadratic_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ crossEquivalent correctionF constantF (correctionData (var 0) (var 1) (var 2) (var 3))
      (correctionQuadratic (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (correction_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeExponentTaylor
