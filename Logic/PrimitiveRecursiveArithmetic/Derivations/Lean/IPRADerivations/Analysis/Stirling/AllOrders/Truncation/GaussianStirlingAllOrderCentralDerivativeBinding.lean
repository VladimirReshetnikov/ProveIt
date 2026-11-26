import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderCentralTaylorBound

/-!
# The central Taylor coefficient is the original derivative sample

The quadratic coefficient in the literal higher Bernoulli grid is
the original lower-degree Bernoulli polynomial on the same grid.
The denominator changes only by the certified coefficient scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralDerivativeBinding

open_ipra
open GaussianStirlingAllOrderCentralTaylor (curvature homogeneous quadratic)
open GaussianStirlingAllOrderCentralTaylorBound (curvatureNumerator curvature_evaluation evaluation)
open BernoulliBounds (bden bint bint_eq pv)
open BernoulliCoefficients (bc bc_deriv)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem coefficient_step (d : ℕ) (j : Fin (d+1)) :
    bint (d+2) j.succ.succ*(quadratic ((j : ℕ)+2) : ℤ)*(bden d : ℤ) =
      bint d j*(bden (d+2) : ℤ) := by
  have h₁ := bc_deriv (d+1) ((j : ℕ)+1)
  have h₂ := bc_deriv d (j : ℕ)
  have hs : quadratic ((j : ℕ)+2) = ((j : ℕ)+2)*((j : ℕ)+1) := by
    unfold quadratic
    congr 1
  have e : ((quadratic ((j : ℕ)+2) : ℕ) : ℚ)*bc (d+2) ((j : ℕ)+2) = bc d (j : ℕ) := by
    rw [hs]
    push_cast at h₁ ⊢
    linear_combination ((j : ℕ)+1:ℚ)*h₁+h₂
  have E : ((bint (d+2) j.succ.succ : ℤ) : ℚ)*(quadratic ((j : ℕ)+2) : ℕ)*(bden d : ℕ) =
      (bint d j : ℚ)*(bden (d+2) : ℕ) := by
    rw [bint_eq,bint_eq]
    simp only [Fin.val_succ]
    linear_combination (bden d : ℚ)*(bden (d+2):ℚ)*e
  exact_mod_cast E

theorem curvature_clearing {R : Type*} [CommRing R] (d : ℕ) (x M : R) :
    curvature (d+2) (bint (d+2)) x M*(bden d : R) =
      homogeneous d (bint d) x M*(bden (d+2) : R) := by
  unfold curvature homogeneous
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show quadratic 0=0 by decide,show quadratic (0+1)=0 by decide,
    Nat.cast_zero,MulZeroClass.mul_zero,MulZeroClass.zero_mul,_root_.zero_add]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e₁ : ((j : ℕ)+1+1)-2 = (j : ℕ) := by omega
  have e₂ : (d+2)-((j : ℕ)+1+1) = d-(j : ℕ) := by omega
  have e₃ : (j : ℕ)+1+1 = (j : ℕ)+2 := by omega
  rw [e₁,e₂,e₃]
  have e := congrArg (fun z : ℤ => (z : R)) (coefficient_step d j)
  push_cast at e
  linear_combination x^(j : ℕ)*M^(d-(j : ℕ))*e

theorem actual_curvature_numerator (d : ℕ) (p M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (curvatureNumerator (d+2) (bint (d+2)) p M*ZT.ofNat (num (bden d)))
      (pv (bint d) p M*ZT.ofNat (num (bden (d+2)))) := by
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,evaluation,curvature_evaluation,IPRA.Q.mk_num,map_natCast]
  exact curvature_clearing d (Groth.ι (IPRA.Q.mk Γ p)) (Groth.ι (IPRA.Q.mk Γ M))

theorem actual_Bernoulli_curvature_numerator_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (ZT.eq (curvatureNumerator (d+2) (bint (d+2)) (var 0) (var 1)*ZT.ofNat (num (bden d)))
        (pv (bint d) (var 0) (var 1)*ZT.ofNat (num (bden (d+2))))) :=
  closeUniv 2 (actual_curvature_numerator d _ _)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralDerivativeBinding
