import GowersSzemeredi.Proofs18GeneralInverseStep

/-! The geometric and modulus conditions for the general inverse step
follow from short polynomial localization, above a finite explicit bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The lower cell-length and no-wrap conditions for the local prime models. -/
def shortLocalizationThreshold (degree : Nat) (e c T Tloc : Real) : Real :=
  max Tloc (max (((degree + 2 : Nat) : Real) ^ (2 : Nat))
    (positivePowerThreshold (c * max 2 T) 1 e))

/-- A short-cell polynomial localization theorem supplies every geometric
hypothesis of the general inverse induction step. The lower-degree inverse
bound is applied in genuinely constructed prime models. -/
theorem FunctionDiscrepancyBound.of_short_polynomial_localization
    {degree : Nat} {alpha eta beta sigma T e c Tloc : Real}
    (hbound : FunctionDiscrepancyBound degree
      ((eta / 2) / (2 * (degree + 2 : Nat) : Real) ^ (degree + 2)) beta sigma T)
    (hη : 0 < eta) (hβ : 0 < beta) (hσ : 0 < sigma) (hσ16 : sigma ≤ 16)
    (he : 0 < e) (hc : 0 < c)
    (hlocal : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (degree + 1) →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn (degree + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ e / c ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) degree eta Q (l + 1)) :
    FunctionDiscrepancyBound (degree + 1) alpha (eta * beta / 4)
      (inverseStepExponent degree e sigma)
      (max (shortLocalizationThreshold degree e c T Tloc)
        (inverseStepThreshold degree eta beta e c sigma)) := by
  apply hbound.of_polynomial_localization hη hβ hσ hσ16 he hc
  intro N _ _ hN f hf hnot
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    hlocal N ((le_max_left _ _).trans hN) f hf hnot
  have hlarge : c * max 2 T ≤ (N : Real) ^ e := by
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN) :
        positivePowerThreshold (c * max 2 T) 1 e ≤ (N : Real))
  have hlmax : max 2 T ≤ (l : Real) := by
    apply le_trans _ hlength
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlarge)
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hlT : T ≤ (l : Real) := (le_max_right 2 T).trans hlmax
  have hNreal : ((degree + 2 : Nat) : Real) ^ (2 : Nat) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hk0 : (0 : Real) ≤ (degree + 2 : Nat) := Nat.cast_nonneg _
  have hroot : ((degree + 2 : Nat) : Real) ≤ Real.sqrt N := by
    nlinarith only [hNreal, hroot0, hrootsq, hk0]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hrootupper : ((degree + 2 : Nat) : Real) * Real.sqrt N ≤ (N : Real) := by
    nlinarith only [hrootsq, hrootprod]
  refine ⟨phi, K, l, l + 1, Q, hpoly, hpart, fun i => (hproper i).1, hl, hlT, by omega, ?_, hlength, hfail⟩
  intro i
  have hs : (degree + 2) * (Q i).length ≤ N := by
    have h := (mul_le_mul_of_nonneg_left (hupper i) hk0).trans hrootupper
    exact_mod_cast h
  rcases (hproper i).2 with hi | hi <;> exact ⟨by omega, by omega, hs⟩

end LeanProofs.GowersSzemeredi
