import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationGrid
import IPRADerivations.Analysis.RationalArithmetic.RationalValueBounds

/-!
# One-sided real order survives signed observation rounding

An upper comparison of the original real coordinates at scale S
yields a lower comparison of the corresponding signed grid difference.
Each of the two signed quotient roundings adds one lattice unit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianSignedObservationOrder

open_ipra
open GaussianSignedObservationGrid (rounded clearedError rounding_band)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive)
open GaussianRationalHorner (positive_product)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper cross crossLeft)
open ComplexLogarithmRemainder (re eval_re_code)
open SignedGridStepBounds (neg_order)
open PolynomialBisection (zle_add zle_congr zle_scale zle_scale_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem scalar_lower (a b S E : PTm n) (h : Γ ⊢[PRAAx] upper a b E S) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (E*denominatorOf a*denominatorOf b)) (-(ZT.ofNat S*cross a b)) := by
  let d := monus (S*crossLeft b a+E*denominatorOf a*denominatorOf b) (S*crossLeft a b)
  have e : Γ ⊢[PRAAx] S*crossLeft b a+E*denominatorOf a*denominatorOf b ≐ S*crossLeft a b+d :=
    eq_add_of_le h
  have eq := natEq e
  apply zle_of_toZ d
  simp only [cross,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  simp only [crossLeft,Q.mk_add,map_add,Q.mk_mul,map_mul] at eq
  simp only [ZT.toZ,Q.mk_mul,map_mul]
  linear_combination -eq

private theorem coordinate_lower (q r S E : PTm n) (h : Γ ⊢[PRAAx] upper (fstT r) (fstT q) E S) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (rawDen q*rawDen r*E))
      (ZT.ofNat S*(ZT.ofNat (rawDen r)*re (rawGaussian q)-ZT.ofNat (rawDen q)*re (rawGaussian r))) := by
  let D := denominatorOf (sndT q)*denominatorOf (sndT r)
  have lower := zle_scale D (scalar_lower _ _ S E h)
  refine zle_congr ?_ ?_ lower
  · simp only [D,rawDen,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_neg,Q.mk_mul,map_mul]
    ring
  · simp only [D,rawDen,rawGaussian,eval_re_code,cross,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_sub,
      ZT.toZ_neg,Q.mk_mul,map_mul]
    ring

theorem lower (q r S E : PTm n) (h : Γ ⊢[PRAAx] upper (fstT r) (fstT q) E S) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (E+two)) (rounded q S-rounded r S) := by
  have first := zle_scale (rawDen r) (rounding_band (Γ := Γ) q S).andE₁
  have last := zle_scale (rawDen q) (neg_order (rounding_band (Γ := Γ) r S).andE₂)
  have joined := zle_add (zle_add (coordinate_lower q r S E h) first) last
  apply zle_scale_cancel (positive_product _ _ (raw_den_positive q) (raw_den_positive r))
  refine zle_congr ?_ ?_ joined
  · simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
    ipra_simps
    ring
  · simp only [clearedError,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ring

theorem actual_signed_observation_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let q := var 0
     let r := var 1
     let S := var 2
     let E := var 3
     upper (fstT r) (fstT q) E S ⟶ zle (-ZT.ofNat (E+two)) (rounded q S-rounded r S)) :=
  closeUniv 4 (.impI (lower _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSignedObservationOrder
