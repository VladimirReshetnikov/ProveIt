/-
A uniform step certificate for the zero-free kept-power logarithm.
The lower margin for the original base power is one over M.
-/
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.RelativeLogarithms.GaussianBarnesCanonicalHeadRelativeLog
import IPRADerivations.Analysis.Barnes.HeadProducts.BasePowers.GaussianBarnesCanonicalHeadPolynomialQuotient
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameReciprocal

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLogMargin

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHeadRelativeLog (relative numerator denominator radius source)
open GaussianBarnesCanonicalHeadPolynomialDerivative (input)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalL1 (raw_den_positive raw_represents)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (R N M : PTm n) : PTm n := M*GaussianBarnesCanonicalHeadPolynomialQuotient.continuityGain R N

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N M : PTm n) :
    Syn.subst σ (gain R N M) = gain (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ M) := by
  simp [gain,GaussianBarnesCanonicalHeadPolynomialQuotient.continuityGain,
    GaussianBarnesCanonicalHeadPolynomialDerivative.errorGain,GaussianBarnesCanonicalHeadPolynomialDerivative.slopeCap]

theorem relative_bound (z h R B H N M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H)
    (hh : Γ ⊢[PRAAx] le H B) (hm : Γ ⊢[PRAAx] le one M)
    (hl : Γ ⊢[PRAAx] GaussianNameReciprocal.lower (powerProduct z B N) M) :
    Γ ⊢[PRAAx] bounded (relative z h B N) (gain R N M*H) B := by
  let a := powerProduct z B N
  let K := GaussianBarnesCanonicalHeadPolynomialQuotient.continuityGain R N
  let v := relative z h B N
  have inverse := GaussianNameReciprocal.inverse_bound a M hm hl
  have difference := GaussianBarnesCanonicalHeadPolynomialQuotient.rational_continuity z h R B H N hs hh
  have product : Γ ⊢[PRAAx] bounded v (M*(K*H)) (one*B) :=
    bounded_product _ _ _ _ _ _ (le_refl one) hs.andE₁ inverse difference
  exact bound_congr (.eqRefl _) (mul_assoc M K H).eqSymm (one_mul B) product

theorem decoded_half_disk (q A B : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hs : Γ ⊢[PRAAx] le (num 4*A) B) : Γ ⊢[PRAAx]
    le (two*GaussianL1.norm1 (GaussianRationalL1.rawGaussian q)) (GaussianRationalL1.rawDen q) := by
  let g := GaussianRationalL1.rawGaussian q
  let d := GaussianRationalL1.rawDen q
  let r := GaussianL1.norm1 g
  let s := ComplexLogarithmRemainder.normSq g
  have hd : Γ ⊢[PRAAx] le one d := raw_den_positive q
  have clear : Γ ⊢[PRAAx] le ((B*B)*s) ((A*A)*(d*d)) :=
    (bounded_iff q g d A B hd hb (raw_represents q)).iffMp hq
  have nr : Γ ⊢[PRAAx] le (r*r) (two*s) := GaussianL1.norm1_square_le_two_normSq g
  have budget : Γ ⊢[PRAAx] le (num 8*(A*A)) (B*B) := by
    have scaled := Common.mul_le_mul hs hs
    have low : Γ ⊢[PRAAx] le (num 8*(A*A)) ((num 4*A)*(num 4*A)) :=
      le_of_eq_add (d := num 8*(A*A)) (by ipra_ring)
    exact le_trans low scaled
  have sq : Γ ⊢[PRAAx] le ((B*B)*((two*r)*(two*r))) ((B*B)*(d*d)) := by
    have p : Γ ⊢[PRAAx] le ((B*B)*((two*r)*(two*r))) (num 8*((B*B)*s)) := by
      have c := mul_le_mul_right (num 4*(B*B)) nr
      exact le_congr (by ipra_ring) (by ipra_ring) c
    have a : Γ ⊢[PRAAx] le (num 8*((B*B)*s)) (num 8*((A*A)*(d*d))) :=
      Common.mul_le_mul (le_refl _) clear
    have v := mul_le_mul_right (d*d) budget
    exact le_trans p (le_trans a (le_congr (by ipra_ring) (.eqRefl _) v))
  exact Common.le_of_sq_le (Common.mul_cancel_le (positive_product _ _ hb hb) sq)

theorem source_of_small (z h R B H N M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H)
    (hh : Γ ⊢[PRAAx] le H B) (hm : Γ ⊢[PRAAx] le one M)
    (hl : Γ ⊢[PRAAx] GaussianNameReciprocal.lower (powerProduct z B N) M)
    (hb : Γ ⊢[PRAAx] le (num 4*(gain R N M*H)) B) :
    Γ ⊢[PRAAx] source z h B N :=
  .andI (GaussianNameReciprocal.lower_norm_positive _ M hm hl)
    (decoded_half_disk _ _ _ hs.andE₁ (relative_bound z h R B H N M hs hh hm hl) hb)

theorem actual_Barnes_kept_power_relative_log_margin_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((input (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
        (le (var 4) (var 3) ⋏ (le one (var 6) ⋏
          (GaussianNameReciprocal.lower (powerProduct (var 0) (var 3) (var 5)) (var 6) ⋏
            le (num 4*(gain (var 2) (var 5) (var 6)*var 4)) (var 3))))) ⟶
        source (var 0) (var 1) (var 3) (var 5)) :=
  closeUniv 7 (.impI (source_of_small _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLogMargin
