import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliCoefficients
import IPRADerivations.AnalyticNumberTheory.RobinThreePos
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Original Bernoulli mesh reflection and endpoint identities

Reflection is first proved for the homogeneous integer polynomial,
so it can be instantiated in the ring of arithmetic terms. The
result concerns the original cleared sampler `BernoulliBounds.pv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (pv bint bint_eq bden zint toZ_zint)
open GaussianStirlingAllOrderBernoulliCoefficients (normalized reflection integer_polynomial_evaluation odd_constant_zero)
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

noncomputable def homogeneous {R : Type*} [CommRing R] (j : ℕ) (p q : R) : R :=
  ∑ i : Fin (j+1), (bint j i : R)*p^(i : ℕ)*q^(j-(i : ℕ))

private theorem rational_homogeneous (j : ℕ) (p q : ℚ) (hq : q ≠ 0) :
    homogeneous j p q = (bden j : ℚ)*(normalized j).eval (p/q)*q^j := by
  rw [← integer_polynomial_evaluation j (p/q), Finset.sum_mul]
  unfold homogeneous
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ j := Nat.lt_succ_iff.mp i.isLt
  have e : (p/q)^(i : ℕ)*q^j = p^(i : ℕ)*q^(j-(i : ℕ)) := by
    rw [div_pow]
    calc
      p^(i : ℕ)/q^(i : ℕ)*q^j = (p^(i : ℕ)/q^(i : ℕ))*(q^(i : ℕ)*q^(j-(i : ℕ))) := by
        rw [← pow_add,Nat.add_sub_of_le hi]
      _ = p^(i : ℕ)*q^(j-(i : ℕ)) := by field_simp
  linear_combination -(bint j i : ℚ)*e

private theorem rational_reflection (j : ℕ) (p q : ℚ) (hq : q ≠ 0) :
    homogeneous j (q-p) q = (-1)^j*homogeneous j p q := by
  have e : (q-p)/q = 1-p/q := by field_simp
  rw [rational_homogeneous j _ q hq,rational_homogeneous j p q hq,e,reflection]
  ring

private theorem map_homogeneous {R S : Type*} [CommRing R] [CommRing S] (F : R →+* S)
    (j : ℕ) (p q : R) : F (homogeneous j p q) = homogeneous j (F p) (F q) := by
  simp [homogeneous]

private theorem universal_reflection (j : ℕ) :
    homogeneous j (MvPolynomial.X (1 : Fin 2)-MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) (MvPolynomial.X 1) =
      (-1)^j*homogeneous j (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) (MvPolynomial.X 1) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  let S : Fin 2 → Set ℚ := fun _ => Set.univ \ {0}
  apply MvPolynomial.funext_set S (fun _ => Set.infinite_univ.diff (Set.finite_singleton 0))
  intro x hx
  have h : x 1 ≠ 0 := by simpa [S] using Set.mem_pi.mp hx (1 : Fin 2) (Set.mem_univ _)
  simp only [MvPolynomial.eval_map]
  simpa only [← MvPolynomial.coe_eval₂Hom,map_homogeneous,map_sub,map_mul,map_pow,map_neg,map_one,MvPolynomial.eval₂Hom_X']
    using rational_reflection j (x 0) (x 1) h

theorem homogeneous_reflection {R : Type*} [CommRing R] (j : ℕ) (p q : R) :
    homogeneous j (q-p) q = (-1)^j*homogeneous j p q := by
  let f : Fin 2 → R := ![p,q]
  have e := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) f) (universal_reflection j)
  simpa only [map_homogeneous,map_sub,map_mul,map_pow,map_neg,map_one,MvPolynomial.eval₂Hom_X',f,
    Matrix.cons_val_zero,Matrix.cons_val_one] using e

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem toZ_value (j : ℕ) (p M : PTm n) :
    ZT.toZ Γ (pv (bint j) p M) = homogeneous j (Groth.ι (IPRA.Q.mk Γ p)) (Groth.ι (IPRA.Q.mk Γ M)) := by
  simp only [pv,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,homogeneous,IPRA.Q.mk_mul,map_mul,
    AnalyticNumberTheory.RobinThreePos.pw_lit]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mesh_reflection (j : ℕ) (p M : PTm n) (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] ZT.eq (pv (bint j) (monus M p) M) (zint ((-1 : ℤ)^j)*pv (bint j) p M) := by
  apply ZT.derive
  simp only [toZ_value,ZT.toZ_mul,toZ_zint,Int.cast_pow,Int.cast_neg,Int.cast_one]
  have e := natEq (eq_add_of_le hp)
  simp only [IPRA.Q.mk_add,map_add] at e
  have h := homogeneous_reflection j (Groth.ι (IPRA.Q.mk Γ p)) (Groth.ι (IPRA.Q.mk Γ M))
  rw [show Groth.ι (IPRA.Q.mk Γ M)-Groth.ι (IPRA.Q.mk Γ p) = Groth.ι (IPRA.Q.mk Γ (monus M p)) by
    conv_lhs => rw [e]
    ring] at h
  exact h

private theorem homogeneous_at_zero {R : Type*} [CommRing R] (j : ℕ) (q : R) :
    homogeneous j 0 q = (bint j 0 : R)*q^j := by
  unfold homogeneous
  rw [Finset.sum_eq_single (0 : Fin (j+1))]
  · simp
  · intro i _ h
    have h0 : (i : ℕ) ≠ 0 := fun z => h (Fin.ext z)
    simp [zero_pow h0]
  · simp

theorem lower_endpoint_value (j : ℕ) (M : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (pv (bint j) zero M) (zint (bint j 0)*ZT.ofNat (pw M (num j))) := by
  apply ZT.derive
  simpa only [toZ_value,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero,AnalyticNumberTheory.RobinThreePos.pw_lit]
    using homogeneous_at_zero j (Groth.ι (IPRA.Q.mk Γ M))

theorem even_endpoints (j : ℕ) (hj : Even j) (M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (pv (bint j) M M) (pv (bint j) zero M) := by
  apply ZT.derive
  have h := ZT.toZ_eq (mesh_reflection (Γ := Γ) j zero M (zero_le M))
  have e := natEq (monus_zero (Γ := Γ) M)
  simp only [toZ_value,ZT.toZ_mul,toZ_zint,hj.neg_one_pow,Int.cast_one,_root_.one_mul,e] at h ⊢
  exact h

theorem odd_endpoints_zero (j : ℕ) (hj : Odd j) (h : 1 < j) (M : PTm n) :
    (Γ ⊢[PRAAx] ZT.eq (pv (bint j) zero M) (ZT.ofNat zero)) ∧
      (Γ ⊢[PRAAx] ZT.eq (pv (bint j) M M) (ZT.ofNat zero)) := by
  have b : bint j 0 = 0 := by
    have e := bint_eq j 0
    rw [show ((0 : Fin (j+1)) : ℕ) = 0 by rfl,odd_constant_zero hj h] at e
    exact_mod_cast (by simpa using e : (bint j 0 : ℚ) = 0)
  have lo : Γ ⊢[PRAAx] ZT.eq (pv (bint j) zero M) (ZT.ofNat zero) := by
    apply ZT.derive
    have e := ZT.toZ_eq (lower_endpoint_value (Γ := Γ) j M)
    simpa [b,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero] using e
  refine ⟨lo,?_⟩
  apply ZT.derive
  have h := ZT.toZ_eq (mesh_reflection (Γ := Γ) j zero M (zero_le M))
  have e := natEq (monus_zero (Γ := Γ) M)
  have l := ZT.toZ_eq lo
  simp [toZ_value,ZT.toZ_mul,l,ZT.toZ_ofNat,IPRA.Q.mk_zero,e] at h ⊢
  exact h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMesh
