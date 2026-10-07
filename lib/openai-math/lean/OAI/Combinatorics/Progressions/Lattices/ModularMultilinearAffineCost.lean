import OAI.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_affine_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f)))
    (offset : (I → ZMod (p ^ a)) → ZMod (p ^ a)) :
    (𝔼 x : I → ZMod (p ^ a), 𝔼 t : ZMod (p ^ a),
      if t * eval x P + offset x = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  let b := (a + 1) / 2
  have hb := modularSublevel_half_depth ha
  let reduce : ZMod (p ^ a) →+* ZMod (p ^ b) :=
    ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
  have hmap : ∀ i, degreeOf i (P.map reduce) ≤ 1 := by
    intro i
    rw [degreeOf_le_iff]
    intro m hm
    exact degreeOf_le_iff.mp (hP i) m (support_map_subset reduce P hm)
  have hunit' : IsUnit ((P.map reduce).coeff ((fullShiftExponent r).mapDomain f)) := by
    rw [coeff_map]
    exact hunit.map reduce
  have hdeg' : (P.map reduce).totalDegree ≤ r := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset reduce P hm)).trans hdeg
  have hsmall := modularMultilinear_sublevel_of_pos hr hp hb.1
    (P.map reduce) f hf hdeg' hmap hunit'
  have hbad : (𝔼 x : I → ZMod (p ^ a),
      if reduce (eval x P) = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ (r - 1)) := by
    change (𝔼 x : I → ZMod (p ^ a),
      if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval x P) = 0
        then (1 : ℝ) else 0) ≤ _
    rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
    exact hsmall
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hfiber (c d : ZMod (p ^ a)) (hc : reduce c ≠ 0) :
      (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
        (p : ℝ) ^ (-(a : ℝ) / 2) := by
    have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
    simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
  have hsplit := modularAffine_zero_split (fun x => eval x P) offset reduce
    (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
  exact hsplit.trans ((add_le_add hbad le_rfl).trans
    (modularSublevel_induction_bound hp1 ha hr))

theorem modularMultilinear_gcd_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), ((eval x P).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have h := modularMultilinear_affine_mean_sublevel hr hp ha P f hf hdeg hP hunit
    (fun _ => 0)
  rw [zmod_gcd_expect_eq_mul_zero_expect (p ^ a) (fun x => eval x P)]
  simpa only [add_zero, mul_comm] using h

end Erdos3

end

end OAI
