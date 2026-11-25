import IPRADerivations.Analysis.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.GaussianCompactLogarithmBounds

/-!
# A uniform disk for the original complex logarithm observations

A right half-plane margin and a common argument disk bound the
squared modulus above and away from zero. The original real
logarithm bound on that interval and the phase sampler bound give
a disk for every original complex logarithm observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmCompactBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactLogarithmBounds (domain)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianNameArithmetic (multiplyData multiplyModulus multiplyRaw addRaw)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (positive_product qmul_canonical qadd_canonical)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (R K : PTm n) : PTm n :=
  GaussianCompactLogarithmBounds.radius (K*K) (R*R)+GaussianRightHalfPlaneArgument.radius

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (R K : PTm n) :
    Syn.subst σ (radius R K) = radius (Syn.subst σ R) (Syn.subst σ K) := by
  simp [radius,GaussianRightHalfPlaneArgument.radius,two]

private theorem radial_bound (p A B D neg R K : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] bounded (ap2 GaussianRightHalfPlaneRadialLogarithm.nameF p
      (GaussianRightHalfPlaneRadialLogarithm.data A B D)) (GaussianCompactLogarithmBounds.radius (K*K) (R*R)) one := by
  let a := normNum A B
  let b := normDen D
  let c : PTm n := GaussianEulerSquareFactorInverse.half
  let x := GaussianPositiveRationalLogarithm.data a b
  let q := GaussianFastValueCut.exponent (multiplyModulus constantF logF c x) p
  have hz := h.andE₁
  have hE := GaussianDominantScalarOrder.factor_positive_left K A (le_trans hz.andE₂ hK)
  have lo₀ : Γ ⊢[PRAAx] le b ((K*K)*(A*A)) :=
    le_congr (.eqRefl b) (by ipra_ring) (sq_le_sq hK)
  have lo₁ : Γ ⊢[PRAAx] le ((K*K)*(A*A)) ((K*K)*a) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (K*K) (le_add_right (A*A) (B*B)))
  have lo := le_trans lo₀ lo₁
  have hi : Γ ⊢[PRAAx] le a ((R*R)*b) := le_congr
    (native_norm A B neg hz.andE₁.andE₂) (by dsimp only [b,normDen]; ipra_ring) h.andE₂
  have dom : Γ ⊢[PRAAx] domain a b (K*K) (R*R) :=
    .andI (GaussianRightHalfPlaneRadialLogarithm.log_source A B D hz.andE₁.andE₁ hz.andE₂) (.andI lo hi)
  have rad := GaussianCompactLogarithmBounds.sample_bound q a b (K*K) (R*R) (positive_product _ _ hE hE) dom
  have half : Γ ⊢[PRAAx] bounded c one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (le_succ_self one)
      (le_of_eq_add (d := one) (by ipra_ring))
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF logF c x p).eqTrans
    (GaussianExponentialReference.recode_fixed (multiplyRaw constantF logF q c x) (qmul_canonical _ _))
  have atConstant := qmul_congr (constant_at (Γ := Γ) q c) (.eqRefl (ap2 logF q x))
  exact bound_congr (read.eqTrans atConstant).eqSymm (one_mul _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) half rad)

theorem sample_bound (p A B D neg R K : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] bounded (ap2 GaussianRightHalfPlaneLogarithm.nameF p
      (GaussianRightHalfPlaneLogarithm.data A B D neg)) (radius R K) one := by
  let F := GaussianRightHalfPlaneRadialLogarithm.nameF
  let G := GaussianRightHalfPlaneArgument.nameF
  let x := GaussianRightHalfPlaneRadialLogarithm.data A B D
  let y := GaussianRightHalfPlaneArgument.data A B neg
  let q := GaussianFastValueCut.exponent two p
  have read := (GaussianNameArithmetic.add_at (Γ := Γ) F G x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (addRaw F G q x y) (qadd_canonical _ _))
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
      (radial_bound q A B D neg R K h hK) (GaussianRightHalfPlaneArgument.name_bound q A B neg h.andE₁.andE₁))

theorem samples_bounded (A B D neg R K : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] sampleBound GaussianRightHalfPlaneLogarithm.nameF
      (GaussianRightHalfPlaneLogarithm.data A B D neg) (radius R K) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s (v : PTm n) := Syn.shift v
  have hs : Δ ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source] using h.shift
  have hm : Δ ⊢[PRAAx] le (s D) (s K*s A) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift
  simpa only [sampleBound,Syn.shift,s,subst_radius,GaussianRightHalfPlaneLogarithm.subst_data] using
    sample_bound (var 0) (s A) (s B) (s D) (s neg) (s R) (s K) hs hm

theorem actual_right_half_plane_logarithm_compact_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 2) (var 5*var 0) ⟶
      sampleBound GaussianRightHalfPlaneLogarithm.nameF
        (GaussianRightHalfPlaneLogarithm.data (var 0) (var 1) (var 2) (var 3)) (radius (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (samples_bounded _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmCompactBound
