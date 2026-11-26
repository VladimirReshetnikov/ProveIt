import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliMesh
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalFiniteSum
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianFactorBudget
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Foundations.NumeralPrimes

/-!
# The actual centered Bernoulli samples in the signed Stirling remainder

At fixed order m this constructs the rational mesh reading of
`(-1)^m (B_(2m)(t) - B_(2m)(0))`. The signed numerator uses the
original cleared polynomial sampler, with the factorial restoring
the paper's unnormalized convention.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCenteredBernoulli

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (bden bden_pos bint pv zint toZ_zint)
open GaussianStirlingAllOrderBernoulliMesh (mesh_reflection even_endpoints)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factor (m : ℕ) : ℤ := (-1)^m * (Nat.factorial (2*m) : ℤ)

def numerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (factor m) * (pv (bint (2*m)) p M-pv (bint (2*m)) zero M)

def denominator (m : ℕ) (M : PTm n) : PTm n :=
  num (bden (2*m))*pw M (num (2*m))

def sample (m : ℕ) (p M : PTm n) : PTm n := normalize (numerator m p M) (denominator m M)

theorem denominator_positive (m : ℕ) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (denominator m M) :=
  GaussianRationalHorner.positive_product _ _
    (Foundations.NumeralPrimes.num_le (a := 1) (bden_pos (2*m))) (GaussianFactorBudget.power_positive _ _ hM)

theorem sample_canonical (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (sample m p M) :=
  normalize_well_formed _ _ (denominator_positive m M hM)

theorem sample_value (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sample m p M) (numerator m p M) (denominator m M) :=
  normalize_preserves_value _ _ (denominator_positive m M hM)

private theorem numerator_reflection (m : ℕ) (p M : PTm n) (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] ZT.eq (numerator m (monus M p) M) (numerator m p M) := by
  have he : Even (2*m) := ⟨m,by omega⟩
  have h := ZT.toZ_eq (mesh_reflection (Γ := Γ) (2*m) p M hp)
  simp only [ZT.toZ_mul,toZ_zint,he.neg_one_pow,Int.cast_one,_root_.one_mul] at h
  apply ZT.derive
  simp only [numerator,ZT.toZ_mul,ZT.toZ_sub,h]

theorem reflected_sample (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] sample m (monus M p) M ≐ sample m p M := by
  have hD := denominator_positive m M hM
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (sample_canonical m _ M hM) (sample_canonical m _ M hM)
    (sample_value m _ M hM) (sample_value m _ M hM) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_eq (numerator_reflection m p M hp)]

private theorem zero_of_numerator (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] ZT.eq (numerator m p M) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] sample m p M ≐ GaussianEuclideanDistanceName.fraction zero one := by
  have hD := denominator_positive m M hM
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (sample_canonical m p M hM)
    (normalize_well_formed _ _ (le_refl one)) (sample_value m p M hM)
    (GaussianEuclideanDistanceName.fraction_represents _ _ (le_refl one)) hD (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_eq h,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

theorem endpoint_samples_zero (m : ℕ) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    (Γ ⊢[PRAAx] sample m zero M ≐ GaussianEuclideanDistanceName.fraction zero one) ∧
      (Γ ⊢[PRAAx] sample m M M ≐ GaussianEuclideanDistanceName.fraction zero one) := by
  constructor
  · apply zero_of_numerator m zero M hM
    apply ZT.derive
    simp [numerator,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
  · apply zero_of_numerator m M M hM
    apply ZT.derive
    have he : Even (2*m) := ⟨m,by omega⟩
    simp [numerator,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero,
      ZT.toZ_eq (even_endpoints (Γ := Γ) (2*m) he M)]

theorem actual_centered_Bernoulli_mesh_reflection_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ le (var 0) (var 1)) ⟶ sample m (monus (var 1) (var 0)) (var 1) ≐ sample m (var 0) (var 1)) :=
  closeUniv 2 (.impI (reflected_sample m _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_centered_Bernoulli_mesh_endpoints_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶
      (sample m zero (var 0) ≐ GaussianEuclideanDistanceName.fraction zero one) ⋏
      (sample m (var 0) (var 0) ≐ GaussianEuclideanDistanceName.fraction zero one)) :=
  closeUniv 1 (.impI (let h := endpoint_samples_zero m (var 0) Prf.hyp0; .andI h.1 h.2))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCenteredBernoulli
