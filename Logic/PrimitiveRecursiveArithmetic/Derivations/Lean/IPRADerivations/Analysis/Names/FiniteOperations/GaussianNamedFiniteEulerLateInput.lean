import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteEuler
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# A common late rational input for the named finite Euler sampler

A requested output is compared to the original certified finite inverse
at any decoded input beyond the stated margin and continuity clocks.
Auxiliary named observations at s+t give a genuine diagonal envelope;
the existing rational finite gap removes only those auxiliary errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteEulerLateInput

open_ipra
open GaussianNamedFiniteEuler (source nameF data modulus late_step name_regular)
open GaussianNamedRightHalfPlane (threshold radius numerator denominator)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def referenceData (f : PR 2) (r x N : PTm n) : PTm n :=
  GaussianBetaAllDegreeEulerInverse.data (numerator f r x) (denominator f r x) N
ipra_subst referenceData

theorem reference_regular (f : PR 2) (r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hm : Γ ⊢[PRAAx] le (threshold A) r) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN GaussianBetaAllDegreeEulerInverse.nameF (referenceData f r x N) :=
  GaussianBetaAllDegreeEulerInverse.name_regular _ (radius f x) _ (two*A) N
    (.andI (GaussianNamedRightHalfPlane.actual_late_source f x A r h.andE₁ hm) h.andE₂)

theorem late_step_wide (f : PR 2) (p q s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hs : Γ ⊢[PRAAx] le s (succ p))
    (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x A N))
      (ap2 GaussianBetaAllDegreeEulerInverse.nameF q (referenceData f r x N))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have clear : Γ ⊢[PRAAx]
      le (rateNumerator one (unit s) (succ p) q*rateDenominator (unit s) p q)
        (rateNumerator one (unit s) p q*rateDenominator (unit s) (succ p) q) := by
    apply le_of_eq_add (d := unit s*unit s*unit p*unit q*unit q)
    apply deriveNat
    have e := natEq dp
    dsimp only [rateNumerator,rateDenominator]
    ipra_simps
    rw [e]
    ring
  exact distance_radius_mono _ _ _ _ _ _
    (denominator_positive _ _ _ (unit_positive s)) (denominator_positive _ _ _ (unit_positive s)) clear
    (late_step f p q s r x A N h hs hm hr)

/-- The comparison uses the same fixed reference input for every t. -/
theorem diagonal_distance (f : PR 2) (t s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) t (data x A N))
      (ap2 GaussianBetaAllDegreeEulerInverse.nameF t (referenceData f r x N))
      (one*unit t+num 4*unit s) (unit s*unit t) := by
  let u := s+t
  let T := unit t
  let U := unit u
  let S := unit s
  have ht := unit_positive (Γ := Γ) t
  have hu := unit_positive (Γ := Γ) u
  have hS := unit_positive (Γ := Γ) s
  have den := positive_product _ _ hS ht
  have hs : Γ ⊢[PRAAx] le s (succ u) := le_trans (le_add_right s t) (le_succ_self u)
  have order : Γ ⊢[PRAAx] le T U := GaussianExponentialReference.unit_monotone (le_add_left t s)
  have point := GaussianNameEquivalence.point_at (nameF f) (data x A N) t u (name_regular f x A N h)
  have first := distance_radius_mono _ _ _ _ two T (positive_product _ _ ht hu) ht
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (T*U) (mul_le_mul_right T order))) point
  have firstScaled := distance_radius_mono _ _ _ _ (two*S) (S*T) ht den
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) first
  have later := late_step_wide f u t s r x A N h hs hm hr
  have second := distance_radius_mono _ _ _ _ (T+two*S) (S*T)
    (denominator_positive _ _ _ hS) den
    (le_congr (by dsimp only [rateNumerator,rateDenominator,T,U,S]; ipra_ring) (by dsimp only [rateDenominator,T,U,S]; ipra_ring)
      (add_le_add_right (S*T*T*U+S*S*T*U) (mul_le_mul_right (S*S*T) order))) later
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den firstScaled second)

theorem diagonal_envelope (f : PR 2) (s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope (nameF f) GaussianBetaAllDegreeEulerInverse.nameF
      (data x A N) (referenceData f r x N) one (unit s) (num 4) := by
  have sh : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have sm : Γ.map Fm.shift ⊢[PRAAx] le (threshold (Syn.shift A)) (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have sr : Γ.map Fm.shift ⊢[PRAAx]
      le (succ (modulus (Syn.shift s) (radius f (Syn.shift x)) (two*Syn.shift A) (Syn.shift N))) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,GaussianNamedFiniteEuler.subst_data,subst_referenceData,
    GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    LeanProofs.IPRA.PTm.subst_num] using
    diagonal_distance f (var 0) (Syn.shift s) (Syn.shift r) (Syn.shift x) (Syn.shift A) (Syn.shift N) sh sm sr

theorem original_independent_rate (f : PR 2) (s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    independentRate (nameF f) GaussianBetaAllDegreeEulerInverse.nameF (data x A N) (referenceData f r x N) one (unit s) :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 4) (unit_positive s)
    (name_regular f x A N h) (reference_regular f r x A N h hm) (diagonal_envelope f s r x A N h hm hr)

/-- There is no upper bound on s in terms of the requested output query. -/
theorem original_observations (f : PR 2) (p q s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x A N))
      (ap2 GaussianBetaAllDegreeEulerInverse.nameF q (referenceData f r x N))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate f s r x A N h hm hr)

theorem original_named_finite_Euler_common_late_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source f (var 4) (var 5) (var 6) ⋏
      (le (threshold (var 5)) (var 3) ⋏
        le (succ (modulus (var 2) (radius f (var 4)) (two*var 5) (var 6))) (var 3))) ⟶
      distanceBounded (ap2 (nameF f) (var 0) (data (var 4) (var 5) (var 6)))
        (ap2 GaussianBetaAllDegreeEulerInverse.nameF (var 1) (referenceData f (var 3) (var 4) (var 6)))
        (rateNumerator one (unit (var 2)) (var 0) (var 1)) (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 7 (.impI (original_observations f _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteEulerLateInput
