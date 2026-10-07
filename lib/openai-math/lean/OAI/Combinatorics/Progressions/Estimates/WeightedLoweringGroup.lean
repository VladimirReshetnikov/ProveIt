/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename

namespace OAI


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLT_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLT w e :=
  fun _ ha => lt_of_lt_of_le (hp ha) hde

theorem weightedSupportLT_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLE w d :=
  fun _ ha => le_of_lt (show _ < d from hp ha)

theorem weightedSupportLT_succ_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w (d + 1)) : p ∈ weightedSupportLE w d :=
  fun _ ha => Nat.lt_succ_iff.mp (hp ha)

theorem weightedSupportLT_zero_eq {w : σ → ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w 0) : p = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro a
  by_contra ha
  exact Nat.not_lt_zero _ (hp (MvPolynomial.mem_support_iff.mpr ha))

theorem weightedLowering_preserves_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p ∈ weightedSupportLE w d := by
  rw [MvPolynomial.aeval_unique F]
  apply weightedSupportLE_aeval w w _ _ hp
  intro i
  simpa only [sub_add_cancel, Function.comp_apply] using (weightedSupportLE w (w i)).add_mem
    (weightedSupportLT_le (hF i)) (weightedSupportLE_X w i)

theorem weightedLowering_mul_bounds (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (hFp : F p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - p ∈ weightedSupportLT w d)
    (hdq : F q - q ∈ weightedSupportLT w e) :
    F (p * q) ∈ weightedSupportLE w (d + e) ∧
      F (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul hFp hFq, ?_⟩
  rw [map_mul, show F p * F q - p * q = (F p - p) * F q + p * (F q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hp hdq)

theorem weightedLowering_monomial_one (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - monomial a 1 ∈ weightedSupportLT w (Finsupp.weight w a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - 1 ∈ _
        rw [map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) hp (weightedLowering_preserves_degree w F hF hp)
          (weightedLowering_preserves_degree w F hF (weightedSupportLE_X w i)) ih (hF i)
        simpa only [X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh.2
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a)
        hp (weightedLowering_preserves_degree w F hF hp)
        (weightedLowering_preserves_degree w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [monomial_mul_monomial, one_mul, map_add] using hh.2

theorem weightedLowering_monomial (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - monomial a r ∈ weightedSupportLT w (Finsupp.weight w a) := by
  have hc : F (C r) = C r := F.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [monomial_mul_monomial, zero_add, mul_one]
  rw [← hm, map_mul, hc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedLowering_monomial_one w F hF a)

theorem weightedLowering_difference (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p - p ∈ weightedSupportLT w d := by
  classical
  change (F.toLinearMap - (LinearMap.id : Module.End R (MvPolynomial σ R))) p ∈
    weightedSupportLT w d
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha) (weightedLowering_monomial w F hF a (p.coeff a))

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialHomDifference
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) : Module.End R (MvPolynomial σ R) :=
  F.toLinearMap - LinearMap.id

theorem polynomialHomDifference_pow_eq_zero (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    (polynomialHomDifference F ^ (d + 1)) p = 0 := by
  induction d generalizing p with
  | zero =>
      rw [pow_one]
      exact weightedSupportLT_zero_eq (weightedLowering_difference w F hF hp)
  | succ d ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (weightedSupportLT_succ_le (weightedLowering_difference w F hF hp))

theorem weightedLowering_eq_zero_of_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) (hz : F p = 0) :
    p = 0 := by
  induction d generalizing p with
  | zero =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      exact neg_eq_zero.mp (weightedSupportLT_zero_eq h)
  | succ d ih =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      have hlow : p ∈ weightedSupportLT w (d + 1) := by
        simpa only [neg_neg] using (weightedSupportLT w (d + 1)).neg_mem h
      exact ih (weightedSupportLT_succ_le hlow) hz

theorem weightedLowering_injective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Injective F := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply weightedLowering_eq_zero_of_degree w F hF
    ((mem_weightedSupportLE_iff w ((p - q).weightedTotalDegree w) (p - q)).mpr le_rfl)
  rw [map_sub, hpq, sub_self]

theorem weightedLowering_preimage_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    ∃ q, q ∈ weightedSupportLE w d ∧ F q = p := by
  induction d generalizing p with
  | zero =>
      exact ⟨p, hp, sub_eq_zero.mp (weightedSupportLT_zero_eq
        (weightedLowering_difference w F hF hp))⟩
  | succ d ih =>
      have hdiff := weightedSupportLT_succ_le (weightedLowering_difference w F hF hp)
      obtain ⟨q, hq, heq⟩ := ih hdiff
      refine ⟨p - q, (weightedSupportLE w (d + 1)).sub_mem hp
        (weightedSupportLE_mono (Nat.le_succ d) hq), ?_⟩
      rw [map_sub, heq]
      abel

theorem weightedLowering_bijective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Bijective F := by
  refine ⟨weightedLowering_injective w F hF, ?_⟩
  intro p
  obtain ⟨q, _, hq⟩ := weightedLowering_preimage_degree w F hF
    ((mem_weightedSupportLE_iff w (p.weightedTotalDegree w) p).mpr le_rfl)
  exact ⟨q, hq⟩

noncomputable def weightedLoweringEquiv (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofBijective F (weightedLowering_bijective w F hF)

theorem weightedLoweringEquiv_apply (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (p : MvPolynomial σ R) :
    weightedLoweringEquiv w F hF p = F p := rfl

theorem weightedLoweringEquiv_inverse_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    (weightedLoweringEquiv w F hF).symm p ∈ weightedSupportLE w d := by
  obtain ⟨q, hq, heq⟩ := weightedLowering_preimage_degree w F hF hp
  have he : weightedLoweringEquiv w F hF q = p := heq
  rw [← he, AlgEquiv.symm_apply_apply]
  exact hq

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

def weightedLoweringSubgroup (w : σ → ℕ) :
    Subgroup (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) where
  carrier := {e | ∀ i, e (X i) - X i ∈ weightedSupportLT w (w i)}
  one_mem' := by
    intro i
    change X i - X i ∈ weightedSupportLT w (w i)
    rw [sub_self]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro e f he hf i
    have hp := weightedLowering_preserves_degree w f.toAlgHom hf (weightedSupportLE_X w i)
    have h := weightedLowering_difference w e.toAlgHom he hp
    change e (f (X i)) - f (X i) ∈ weightedSupportLT w (w i) at h
    change e (f (X i)) - X i ∈ weightedSupportLT w (w i)
    simpa only [sub_add_sub_cancel] using (weightedSupportLT w (w i)).add_mem h (hf i)
  inv_mem' := by
    intro e he i
    obtain ⟨q, hq, hqe⟩ := weightedLowering_preimage_degree w e.toAlgHom he
      (weightedSupportLE_X w i)
    change e q = X i at hqe
    have heq : e.symm (X i) = q := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hqe.symm
    change e.symm (X i) - X i ∈ weightedSupportLT w (w i)
    rw [heq]
    have h := weightedLowering_difference w e.toAlgHom he hq
    change e q - q ∈ weightedSupportLT w (w i) at h
    rw [hqe] at h
    simpa only [neg_sub] using (weightedSupportLT w (w i)).neg_mem h

abbrev WeightedLoweringAut (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(weightedLoweringSubgroup (R := R) w)

theorem weightedLoweringEquiv_mem (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    weightedLoweringEquiv w F hF ∈ weightedLoweringSubgroup w := hF

noncomputable def WeightedLoweringAut.ofHom (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : WeightedLoweringAut w R :=
  ⟨weightedLoweringEquiv w F hF, weightedLoweringEquiv_mem w F hF⟩

theorem WeightedLoweringAut.preserves_degree {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p ∈ weightedSupportLE w d :=
  weightedLowering_preserves_degree w e.val.toAlgHom e.property hp

theorem WeightedLoweringAut.difference_lower {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p - p ∈ weightedSupportLT w d :=
  weightedLowering_difference w e.val.toAlgHom e.property hp

end Erdos3

end OAI
