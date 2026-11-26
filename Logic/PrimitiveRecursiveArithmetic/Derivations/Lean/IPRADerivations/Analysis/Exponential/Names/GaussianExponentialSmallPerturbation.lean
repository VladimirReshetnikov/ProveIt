import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailExponential

/-!
# Exact small-exponent perturbations for the original exponential name

If B≥1, A≤B and the original rational point q has modulus at most A/B,
EVERY actual finite scalar exponential is within 3A/B of one. Thus the
original unit-disk exponential name has the same exact bound at each of
its literal scheduled observations whenever the input observations have
that numerical bound. Input regularity separately derives a regular
output name. Multiplication by an original canonical prefactor bounded
by M gives the exact error 3MA/B, including at zeros of the prefactor.

For source Gamma C10, A=R²+R and B=N give its numerical perturbation and
prefactor bounds once the actual C8 factor identity and its small input
bound are supplied. Those identities are not assumptions of the finite
or named perturbation theorems below.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialSmallPerturbation

open_ipra
open GaussianRationalHorner (qzero qmul canonical)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianUnitDiskExponentialName (sample query shifted index nameF)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem unit_disk_of_small_bound (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] bounded q one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hB (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hAB) hq

/-- Arbitrary numerical cutoff, with the exact original scalar exponential. -/
theorem finite_perturbation (q A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone (num 3*A) B :=
  distance_congr (.eqRefl _) (GaussianGammaCanonicalTailExponential.scalar_zero_point K) (.eqRefl _) (.eqRefl _)
    (GaussianRationalExponentialLipschitz.scalar_sum_lipschitz q qzero A B K hB
      (unit_disk_of_small_bound q A B hB hAB hq) (GaussianMonicResidualRadius.zero_bounded one one (le_refl one))
      ((GaussianReconstructionRoots.distance_zero_iff q A B hB).iffMpr hq))

/-- The original name's literal query is p+4; no additional observation error is needed. -/
theorem sample_perturbation (f : PR 2) (p x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded (query f p x) A B) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x) qone (num 3*A) B :=
  distance_congr (GaussianUnitDiskExponentialName.sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_perturbation (query f p x) A B (index p) hB hAB hq)

def smallSamples (f : PR 2) (x A B : PTm n) : Fm PTm n :=
  .all (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift A) (Syn.shift B))
def nearOneSamples (f : PR 2) (x A B : PTm n) : Fm PTm n :=
  .all (distanceBounded (sample f (var 0) (Syn.shift x)) qone (num 3*Syn.shift A) (Syn.shift B))
ipra_subst smallSamples [Syn.subst_shift, Syn.shift_subst]
ipra_subst nearOneSamples [Syn.subst_shift, Syn.shift_subst]

theorem small_samples_at (f : PR 2) (x A B p : PTm n) (h : Γ ⊢[PRAAx] smallSamples f x A B) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) A B := by simpa [smallSamples] using h.allE p

theorem uniformly_small_perturbation (f : PR 2) (p x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (h : Γ ⊢[PRAAx] smallSamples f x A B) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x) qone (num 3*A) B :=
  sample_perturbation f p x A B hB hAB (small_samples_at f x A B (shifted p) h)

theorem exponential_input (f : PR 2) (x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hc : Γ ⊢[PRAAx] pointCN f x)
    (h : Γ ⊢[PRAAx] smallSamples f x A B) : Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input f x := by
  refine .andI hc (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] smallSamples f (Syn.shift x) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ab : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hAB.shift
  exact unit_disk_of_small_bound _ _ _ bs ab (small_samples_at f _ _ _ (var 0) hs)

theorem regular_near_one (f : PR 2) (x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hc : Γ ⊢[PRAAx] pointCN f x)
    (h : Γ ⊢[PRAAx] smallSamples f x A B) :
    Γ ⊢[PRAAx] pointCN (nameF f) x ⋏ nearOneSamples f x A B := by
  refine .andI (GaussianUnitDiskExponentialName.name_regular f x (exponential_input f x A B hB hAB hc h)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] smallSamples f (Syn.shift x) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ab : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hAB.shift
  simpa only [nearOneSamples] using uniformly_small_perturbation f (var 0) (Syn.shift x) (Syn.shift A) (Syn.shift B) bs ab hs

/-- Exact 3MA/B, obtained by multiplication; the prefactor may vanish. -/
theorem finite_prefactor_perturbation (P q A B M K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (hP : Γ ⊢[PRAAx] bounded P M one) (hc : Γ ⊢[PRAAx] canonical P) :
    Γ ⊢[PRAAx] distanceBounded (qmul P (scalarSum q K)) P (num 3*M*A) B :=
  distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (GaussianPolynomialDeterminantTerms.one_mul_canonical P hc) (by ipra_ring) (.eqRefl _)
    (GaussianNameRingLaws.product_left_error _ _ _ (num 3*A) B M one hB
      (finite_perturbation q A B K hB hAB hq) hP GaussianRationalReciprocal.qone_bounded)

theorem sample_prefactor_perturbation (f : PR 2) (P p x A B M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (h : Γ ⊢[PRAAx] smallSamples f x A B)
    (hP : Γ ⊢[PRAAx] bounded P M one) (hc : Γ ⊢[PRAAx] canonical P) :
    Γ ⊢[PRAAx] distanceBounded (qmul P (sample f p x)) P (num 3*M*A) B :=
  distance_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianUnitDiskExponentialName.sample_at f p x)).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_prefactor_perturbation P (query f p x) A B M (index p) hB hAB
      (small_samples_at f x A B (shifted p) h) hP hc)

theorem original_all_cutoff_small_exponential_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ bounded (var 0) (var 1) (var 2) ⟶
      distanceBounded (scalarSum (var 0) (var 3)) qone (num 3*var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (finite_perturbation _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_regular_small_exponential_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ pointCN f (var 0) ⟶ smallSamples f (var 0) (var 1) (var 2) ⟶
      pointCN (nameF f) (var 0) ⋏ nearOneSamples f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (regular_near_one f _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem original_small_exponential_prefactor_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le (var 2) (var 3) ⟶ bounded (var 1) (var 2) (var 3) ⟶
      bounded (var 0) (var 4) one ⟶ canonical (var 0) ⟶
        distanceBounded (qmul (var 0) (scalarSum (var 1) (var 5))) (var 0) (num 3*var 4*var 2) (var 3)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (finite_prefactor_perturbation _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianExponentialSmallPerturbation
