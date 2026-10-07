import GowersSzemeredi.Proofs16PowerCoverFiniteUnion

/-! Uniform controls for a union with only an upper bound on its number
of pieces. Capping the one-step exponent at one handles all parameter ranges. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem LargeBoxMultilinearCover.weaken {N k : Nat} [NeZero N]
    {Gamma : Finset (Point N k × ZMod N)} {rho sigma C D e f T U : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T)
    (hrs : rho ≤ sigma) (hCD : C ≤ D) (hfe : f ≤ e) (hTU : T ≤ U) (hU : 1 ≤ U) :
    LargeBoxMultilinearCover Gamma sigma D f U := by
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ :=
    h.loss_mono hrs P hP (hTU.trans hT)
  refine ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq.trans hCD, ?_, hmu, hc⟩
  intro j
  exact (Real.rpow_le_rpow_of_exponent_le (hU.trans hT) hfe).trans (hw j)

theorem section16PowerIterationThreshold_monotone (T e : Real) :
    Monotone (section16PowerIterationThreshold T e) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem section16PowerIterationThreshold_one_le (T e : Real) (r : Nat) :
    1 ≤ section16PowerIterationThreshold T e r :=
  section16PowerIterationThreshold_monotone T e (Nat.zero_le r)

/-- At most `R` pieces have a common cover with controls independent of
the actual piece count. The exponent remains strictly positive when `e > 0`. -/
theorem LargeBoxMultilinearCover.bounded_finsetUnion {N k r R : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N k × ZMod N)) {rho C e T : Real}
    (hG : ∀ i, LargeBoxMultilinearCover (Gamma i) rho C e T)
    (hr : r ≤ R) (hρ : 0 ≤ rho) (he : 0 < e) (hC : 0 ≤ C) :
    LargeBoxMultilinearCover (section16FinsetUnion Gamma) ((R : Real) * rho)
      ((R : Real) * C) ((min e 1) ^ R)
      (section16PowerIterationThreshold (max 1 T) (min e 1) R) := by
  have he0 : 0 < min e 1 := lt_min he zero_lt_one
  have hlocal (i : Fin r) := (hG i).weaken le_rfl le_rfl (min_le_left e 1)
    (le_max_right 1 T) (le_max_left 1 T)
  have h := LargeBoxMultilinearCover.finsetUnion Gamma hlocal he0 hC
  have hr' : (r : Real) ≤ R := by exact_mod_cast hr
  exact h.weaken (mul_le_mul_of_nonneg_right hr' hρ)
    (mul_le_mul_of_nonneg_right hr' hC)
    (pow_le_pow_of_le_one he0.le (min_le_right e 1) hr)
    (section16PowerIterationThreshold_monotone _ _ hr)
    (section16PowerIterationThreshold_one_le _ _ R)

end LeanProofs.GowersSzemeredi
