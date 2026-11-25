import IPRADerivations.Analysis.GaussianStirlingAllOrderBernoulliMeshOrder

/-!
# Refinement invariance of the centered Bernoulli sampler

Jointly scaling the numerator and denominator of the grid point
preserves the literal canonical rational code. This keeps the coarse
reference values at 1/8 and 3/8 on every refined mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderBernoulliMesh (homogeneous toZ_value)
open GaussianStirlingAllOrderCenteredBernoulli
  (numerator denominator sample sample_value sample_canonical denominator_positive)
open GaussianRationalHorner (positive_product)
open BernoulliBounds (toZ_zint)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem homogeneous_scale {R : Type*} [CommRing R] (j : ℕ) (S p M : R) :
    homogeneous j (S*p) (S*M) = S^j*homogeneous j p M := by
  unfold homogeneous
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : S^(i : ℕ)*S^(j-(i : ℕ)) = S^j := by
    rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
  simp only [mul_pow]
  linear_combination ((BernoulliBounds.bint j i : R)*p^(i : ℕ)*M^(j-(i : ℕ)))*e

theorem numerator_scale (m : ℕ) (S p M : PTm n) :
    ZT.toZ Γ (numerator m (S*p) (S*M)) = (𝔞 S)^(2*m)*ZT.toZ Γ (numerator m p M) := by
  have ez := homogeneous_scale (2*m) (𝔞 S) 0 (𝔞 M)
  simp only [MulZeroClass.mul_zero] at ez
  simp only [numerator,ZT.toZ_mul,ZT.toZ_sub,toZ_zint,toZ_value,IPRA.Q.mk_mul,map_mul,
    IPRA.Q.mk_zero,map_zero,homogeneous_scale,ez]
  ring

theorem denominator_scale (m : ℕ) (S M : PTm n) :
    𝔞(denominator m (S*M)) = (𝔞 S)^(2*m)*𝔞(denominator m M) := by
  simp only [denominator,IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit,mul_pow]
  ring

theorem sample_refinement (m : ℕ) (S p M : PTm n) (hS : Γ ⊢[PRAAx] le one S) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] sample m (S*p) (S*M) ≐ sample m p M := by
  have hSM := positive_product S M hS hM
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (sample_canonical m _ _ hSM) (sample_canonical m _ _ hM)
    (sample_value m _ _ hSM) (sample_value m _ _ hM) (denominator_positive m _ hSM) (denominator_positive m _ hM)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,numerator_scale,denominator_scale]
  ring

theorem actual_centered_Bernoulli_grid_refinement_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ le one (var 2)) ⟶
      sample m (var 0*var 1) (var 0*var 2) ≐ sample m (var 1) (var 2)) :=
  closeUniv 3 (.impI (sample_refinement m _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshRefinement
