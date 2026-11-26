import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderCentralBernoulliError

/-!
# Quantitative double vanishing at the Bernoulli panel endpoints

Removing the constant term and the exactly zero linear term leaves a
literal square of the distance to the endpoint. This bounds the
adjacent cross-product boundary terms of the discrete parts identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderEndpointError

open_ipra
open GaussianStirlingAllOrderCenteredBernoulli
  (factor numerator denominator sample sample_value denominator_positive reflected_sample)
open GaussianStirlingAllOrderBernoulliMesh (lower_endpoint_value)
open GaussianStirlingAllOrderBernoulliCoefficients (odd_constant_zero)
open GaussianStirlingAllOrderCentralTaylor (homogeneous)
open GaussianStirlingAllOrderCentralTaylorBound (evaluation)
open GaussianStirlingAllOrderCentralBernoulliError (degree radiusDenominator radius_denominator_positive)
open BernoulliBounds (bint bint_eq bden pv zint toZ_zint poly_upper)
open BernoulliCoefficients (bc_deriv)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def coefficient (m : ℕ) (j : Fin (2*m+1)) : ℤ := factor (m+1)*bint (degree m) j.succ.succ

def endpointCoefficient (m : ℕ) : ℕ := ∑ j : Fin (2*m+1), (coefficient m j).natAbs

private theorem linear_zero (m : ℕ) (hm : 0<m) : bint (degree m) 1 = 0 := by
  have hz := odd_constant_zero (j := 2*m+1) ⟨m,by omega⟩ (by omega)
  have e := bc_deriv (2*m+1) 0
  rw [hz] at e
  have e' := bint_eq (degree m) (1 : Fin (degree m+1))
  have d : degree m = (2*m+1)+1 := by unfold degree; omega
  have he : BernoulliCoefficients.bc (degree m) 1 = 0 := by
    simpa [d] using e
  have E : ((bint (degree m) (1 : Fin (degree m+1)) : ℤ) : ℚ)=0 := by
    rw [e']
    change BernoulliCoefficients.bc (degree m) 1*(bden (degree m) : ℚ)=0
    rw [he]
    ring
  exact_mod_cast E

private theorem factorization {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d+3) → ℤ) (z : ℤ)
    (hz : a ((0 : Fin (d+2)).succ)=0) (p M : R) :
    (z : R)*(homogeneous (d+2) a p M-(a 0 : R)*M^(d+2)) =
      p*p*homogeneous d (fun j => z*a j.succ.succ) p M := by
  have split (f : Fin (d+3) → R) : (∑ j, f j) =
      f 0+f ((0 : Fin (d+2)).succ)+∑ j : Fin (d+1), f j.succ.succ := by
    rw [Fin.sum_univ_succ f,Fin.sum_univ_succ (fun j : Fin (d+2) => f j.succ)]
    ring
  unfold homogeneous
  rw [split (fun j => (a j : R)*p^(j : ℕ)*M^(d+2-(j : ℕ)))]
  simp only [Fin.val_zero,Fin.val_succ,pow_zero, _root_.mul_one,Nat.sub_zero]
  rw [hz]
  have cancel (u v : R) : u+v-u=v := by ring
  simp only [Int.cast_zero,MulZeroClass.zero_mul,_root_.zero_add,_root_.add_zero,cancel,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e₁ : d+2-((j : ℕ)+1+1)=d-(j : ℕ) := by omega
  rw [e₁,pow_succ,pow_succ]
  simp only [Int.cast_mul]
  ring

theorem factorized_homogeneous {R : Type*} [CommRing R] (m : ℕ) (hm : 0<m) (p M : R) :
    (factor (m+1) : R)*(homogeneous (degree m) (bint (degree m)) p M -
      (bint (degree m) 0 : R)*M^(degree m)) =
        p*p*homogeneous (2*m) (coefficient m) p M :=
  factorization (2*m) (bint (degree m)) (factor (m+1)) (linear_zero m hm) p M

theorem numerator_factor (m : ℕ) (hm : 0<m) (p M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numerator (m+1) p M) (ZT.ofNat (p*p)*pv (coefficient m) p M) := by
  apply ZT.derive
  have e := ZT.toZ_eq (lower_endpoint_value (Γ := Γ) (degree m) M)
  simp only [ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,AnalyticNumberTheory.RobinThreePos.pw_lit] at e
  simp only [numerator,ZT.toZ_mul,ZT.toZ_sub,toZ_zint,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul]
  change (factor (m+1) : Groth (IPRA.Q Γ))*
    (ZT.toZ Γ (pv (bint (degree m)) p M)-ZT.toZ Γ (pv (bint (degree m)) (ConciseIPRA.PTm.zero : PTm n) M)) = _
  rw [e,evaluation,evaluation]
  exact factorized_homogeneous m hm (𝔞 p) (𝔞 M)

theorem endpoint_upper (m : ℕ) (hm : 0<m) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] rationalLE (sample (m+1) p M) (fraction (num (endpointCoefficient m)*(p*p)) (radiusDenominator m M)) := by
  let A := num (endpointCoefficient m)*(p*p)
  let D := denominator (m+1) M
  let E := radiusDenominator m M
  let W := pw M (num (2*m))
  have hD := denominator_positive (m+1) M hM
  have hE := radius_denominator_positive m M hM
  have ep : 𝔞 D = 𝔞 E*𝔞 W := by
    dsimp only [D,E,W,denominator,radiusDenominator,degree]
    simp only [IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit]
    rw [show 2*(m+1)=2*m+2 by omega,pow_add]
    ring
  have hv := ZT.toZ_eq (numerator_factor (Γ := Γ) m hm p M)
  have old := poly_upper (coefficient m) (by exact Nat.le_refl (endpointCoefficient m)) hp
  apply RationalArithmetic.order_of_representations _ _ _ _ D E (sample_value (m+1) p M hM) (fraction_represents _ _ hE) hD hE
  apply zle_of_comb (𝔞 E*𝔞 p*𝔞 p*zsl old)
  · simp only [zsl_def,ZT.toZ_ofNat,ZT.toZ_mul] at hv ⊢
    ipra_simps
    rw [ep,hv]
    ring
  · exact nn_mul (nn_mul (nn_mul (nn_term E) (nn_term p)) (nn_term p)) (nn_zsl old)

theorem reflected_endpoint_upper (m : ℕ) (hm : 0<m) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] rationalLE (sample (m+1) (monus M p) M) (fraction (num (endpointCoefficient m)*(p*p)) (radiusDenominator m M)) :=
  rationalLE_congr (reflected_sample (m+1) p M hM hp).eqSymm (.eqRefl _) (endpoint_upper m hm p M hM hp)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderEndpointError
