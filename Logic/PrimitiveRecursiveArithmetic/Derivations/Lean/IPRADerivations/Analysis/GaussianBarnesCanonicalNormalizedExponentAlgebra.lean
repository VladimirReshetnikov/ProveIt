import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorShiftAlgebra

/-!
# Exact logarithmic normalization of the Barnes recurrence

The cleared finite exponent, the terminal logarithm, the Gauss
logarithm, and the factorial logarithm combine to the sum of
the harmonic and terminal remainders minus the Stirling remainder.
This calculation allows arbitrary rational observations of the names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedExponentAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add mul neg scale oneCode)
open GaussianRationalHorner (qadd qmul qadd_represents qmul_represents represents represents_rescale
  represents_congr canonical_unique positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents qnegative qnegative_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_neg im_neg re_scale im_scale re_mul im_mul re_one im_one)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def prefixShift (s h c γ H K : PTm n) : PTm n :=
  qadd (qadd s (qadd (qnegative h) (qmul (qnegative c) (qadd qone γ)))) (qsub (qmul c H) K)

def normalized (s h c γ H K T L G : PTm n) : PTm n :=
  qsub (qadd (qadd (prefixShift s h c γ H K) T) (qmul (qsub K (qadd c h)) L)) G

def remainder (s h c γ H K T L G : PTm n) : PTm n :=
  qsub (qadd (qmul (qsub (qadd (qnegative γ) H) L) c) (qsub T (qadd c h)))
    (qsub (qadd (qsub G (qmul (qsub K h) L)) K) s)

theorem normalize (s h c γ H K T L G : PTm n) : Γ ⊢[PRAAx]
    normalized s h c γ H K T L G ≐ remainder s h c γ H K T L G := by
  let ds := rawDen s
  let dh := rawDen h
  let dc := rawDen c
  let dy := rawDen γ
  let da := rawDen H
  let dk := rawDen K
  let dt := rawDen T
  let dl := rawDen L
  let dg := rawDen G
  let D := ds*dh*dc*dy*da*dk*dt*dl*dg
  let E := D*D
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ (raw_den_positive s)
      (raw_den_positive h)) (raw_den_positive c)) (raw_den_positive γ)) (raw_den_positive H)) (raw_den_positive K))
        (raw_den_positive T)) (raw_den_positive L)) (raw_den_positive G)
  have hE := positive_product D D hD hD
  let S := scale (dh*dc*dy*da*dk*dt*dl*dg) (rawGaussian s)
  let A := scale (ds*dc*dy*da*dk*dt*dl*dg) (rawGaussian h)
  let C := scale (ds*dh*dy*da*dk*dt*dl*dg) (rawGaussian c)
  let Y := scale (ds*dh*dc*da*dk*dt*dl*dg) (rawGaussian γ)
  let B := scale (ds*dh*dc*dy*dk*dt*dl*dg) (rawGaussian H)
  let N := scale (ds*dh*dc*dy*da*dt*dl*dg) (rawGaussian K)
  let U := scale (ds*dh*dc*dy*da*dk*dl*dg) (rawGaussian T)
  let V := scale (ds*dh*dc*dy*da*dk*dt*dg) (rawGaussian L)
  let W := scale (ds*dh*dc*dy*da*dk*dt*dl) (rawGaussian G)
  have rs : Γ ⊢[PRAAx] represents s S D := rescale_to _ _ _ _ _ (raw_represents s) (by dsimp [D,ds]; ipra_ring)
  have rh : Γ ⊢[PRAAx] represents h A D := rescale_to _ _ _ _ _ (raw_represents h) (by dsimp [D,dh]; ipra_ring)
  have rc : Γ ⊢[PRAAx] represents c C D := rescale_to _ _ _ _ _ (raw_represents c) (by dsimp [D,dc]; ipra_ring)
  have ry : Γ ⊢[PRAAx] represents γ Y D := rescale_to _ _ _ _ _ (raw_represents γ) (by dsimp [D,dy]; ipra_ring)
  have ra : Γ ⊢[PRAAx] represents H B D := rescale_to _ _ _ _ _ (raw_represents H) (by dsimp [D,da]; ipra_ring)
  have rk : Γ ⊢[PRAAx] represents K N D := rescale_to _ _ _ _ _ (raw_represents K) (by dsimp [D,dk]; ipra_ring)
  have rt : Γ ⊢[PRAAx] represents T U D := rescale_to _ _ _ _ _ (raw_represents T) (by dsimp [D,dt]; ipra_ring)
  have rl : Γ ⊢[PRAAx] represents L V D := rescale_to _ _ _ _ _ (raw_represents L) (by dsimp [D,dl]; ipra_ring)
  have rg : Γ ⊢[PRAAx] represents G W D := rescale_to _ _ _ _ _ (raw_represents G) (by dsimp [D,dg]; ipra_ring)
  let lift {q a : PTm n} (h : Γ ⊢[PRAAx] represents q a D) : Γ ⊢[PRAAx] represents q (scale D a) E :=
    represents_rescale q a D D h
  let sum {q r a b : PTm n} (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E) :=
    qadd_represents q r a b E hE hq hr
  let diff {q r a b : PTm n} (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E) :=
    qsub_represents q r a b E hE hq hr
  let sum1 {q r a b : PTm n} (hq : Γ ⊢[PRAAx] represents q a D) (hr : Γ ⊢[PRAAx] represents r b D) :=
    qadd_represents q r a b D hD hq hr
  let diff1 {q r a b : PTm n} (hq : Γ ⊢[PRAAx] represents q a D) (hr : Γ ⊢[PRAAx] represents r b D) :=
    qsub_represents q r a b D hD hq hr
  let product {q r a b : PTm n} (hq : Γ ⊢[PRAAx] represents q a D) (hr : Γ ⊢[PRAAx] represents r b D) :=
    qmul_represents q r a b D D hD hD hq hr
  let negate {q a : PTm n} (hq : Γ ⊢[PRAAx] represents q a D) := qnegative_represents q a D hq
  have left := diff (sum (sum (sum (sum (lift rs) (sum (lift (negate rh))
    (product (negate rc) (sum1 (qone_represents_scaled D) ry)))) (diff (product rc ra) (lift rk))) (lift rt))
    (product (diff1 rk (sum1 rc rh)) rl)) (lift rg)
  have right := diff (sum (product (diff1 (sum1 (negate ry) ra) rl) rc) (lift (diff1 rt (sum1 rc rh))))
    (diff (sum (diff (lift rg) (product (diff1 rk rh) rl)) (lift rk)) (lift rs))
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (qsub_canonical _ _) hE left
  apply represents_congr (.eqRefl _) _ (.eqRefl _) right
  apply equal_of_values <;> simp only [re_add,im_add,re_sub,im_sub,re_neg,im_neg,re_scale,im_scale,
    re_mul,im_mul,re_one,im_one] <;> ring

theorem actual_Barnes_normalized_exponent_algebra_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (normalized (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (normalize _ _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedExponentAlgebra
