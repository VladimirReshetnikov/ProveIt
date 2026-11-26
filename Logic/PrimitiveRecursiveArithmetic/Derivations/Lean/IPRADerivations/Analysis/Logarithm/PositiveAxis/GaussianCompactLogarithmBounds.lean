import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Core.CertificateTactics

/-!
# Actual logarithm bounds on an original positive compact time interval

This conservative supplier keeps the original Gaussian fraction a/b and
its actual observation clocks. It derives a uniform numerical sample
disk and exact local variation from the proved original harmonic bounds.
No logarithm/output modulus is supplied as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactLogarithmBounds

open_ipra
open GaussianPositiveRationalLogarithm (fraction source sample logF data name_regular)
open GaussianPositiveRationalLogarithmVariation (native crossNumerator cross_norm)
open RationalHarmonicIntervalVariation (gap)
open GaussianRationalHorner (ofGaussian positive_product represents_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def domain (a b E T : PTm n) : Fm PTm n := source a b ⋏ (le b (E*a) ⋏ le a (T*b))
def radius (E T : PTm n) : PTm n := E*(T+one)+num 25
ipra_subst domain
ipra_subst radius

theorem natural_native (a : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale a oneCode) (native a) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,
      native,RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
  all_goals try ipra_simps
  all_goals ring

theorem original_gaussian_time_distance (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    le (D*gap a b c d) (A*b*d) := by
  let V := b*d
  have pos := positive_product (Γ := Γ) _ _ hb hd
  have left := represents_congr (.eqRefl _) (natural_native a) (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (scale a oneCode) b hb)
  have right := represents_congr (.eqRefl _) (natural_native c) (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (scale c oneCode) d hd)
  have l := GaussianRationalSyntheticDivision.rescale_to (fraction a b) (native a) b d V left (.eqRefl _)
  have r := GaussianRationalSyntheticDivision.rescale_to (fraction c d) (native c) d b V right (mul_comm _ _)
  have clear := (GaussianRationalMetric.bounded_difference_iff _ _ _ _ V A D pos hD l r).iffMp h
  have square : Γ ⊢[PRAAx] le ((D*gap a b c d)*(D*gap a b c d)) ((A*b*d)*(A*b*d)) :=
    le_congr ((congrMul (.eqRefl (D*D)) (cross_norm (Γ := Γ) a b c d)).eqTrans (by ipra_ring)) (by dsimp [V]; ipra_ring) clear
  exact nat_sqrt_mono square

theorem original_log_rate (a b c d E A D : PTm n) (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d)
    (hD : Γ ⊢[PRAAx] le one D) (hl : Γ ⊢[PRAAx] le b (E*a)) (hr : Γ ⊢[PRAAx] le d (E*c))
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate logF logF (data a b) (data c d) (E*A) D := by
  have close := original_gaussian_time_distance a b c d A D hab.andE₂ hcd.andE₂ hD h
  have env : Γ ⊢[PRAAx] GaussianNamedLipschitzRate.diagonalEnvelope logF logF (data a b) (data c d) (E*A) D (num 17) := by
    have abs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hab.shift
    have cds : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hcd.shift
    have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hD.shift
    have ls : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift E*Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hl.shift
    have rs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift E*Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hr.shift
    have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift D*gap (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d))
        (Syn.shift A*Syn.shift b*Syn.shift d) := by simpa [Fm.shift,Syn.shift] using close.shift
    refine .allI ?_
    simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
      GaussianNamedLipschitzRate.diagonalDenominator,sample,GaussianPositiveRationalLogarithm.subst_data,
      PTm.subst_mul,PTm.subst_num,Syn.shift] using GaussianPositiveRationalLogarithmVariation.diagonal_native
        (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift E) (Syn.shift A) (Syn.shift D) abs cds ds ls rs cs
  exact GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ hD (name_regular a b hab) (name_regular c d hcd) env

theorem gap_to_one (a b T : PTm n) (h : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx] le (gap a b one one) ((T+one)*b) := by
  have eg : Γ ⊢[PRAAx] gap a b one one ≐ Probability.Variance.ad a b :=
    congrAdd (congrMonus (by ipra_ring) (by ipra_ring)) (congrMonus (by ipra_ring) (by ipra_ring))
  have abs : Γ ⊢[PRAAx] le (Probability.Variance.ad a b*Probability.Variance.ad a b) ((a+b)*(a+b)) := by
    refine le_of_eq_add (d := num 4*a*b) ?_
    ipra_lc -natEq (Probability.Variance.ad_sq (Γ := Γ) a b)
  have sq := le_congr (congrMul eg eg).eqSymm (.eqRefl _) abs
  have first := nat_sqrt_mono sq
  exact le_trans first (le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ h (le_refl b)))

theorem interval_one (Q : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (RationalHarmonicInterval.interval one one Q) ≐
    GaussianRationalHorner.qzero :=
  (GaussianPositiveRationalLogarithmProperness.original_finite_difference one one Q (le_refl one) (le_refl one)).eqSymm.eqTrans
    (GaussianCoefficientNormOrder.qsub_self _)

theorem sample_one_bound (p : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (sample p one one) GaussianRationalHorner.qzero (num 8) (unit p) :=
  distance_congr (.eqRefl _) (interval_one (GammaEulerConstantName.mesh p)) (.eqRefl _) (.eqRefl _)
    (GaussianPositiveRationalLogarithmProperness.sample_interval_error p one one (.andI (le_refl _) (le_refl _)))

/-- Every ORIGINAL logarithm observation has one common numerical disk,
independent of the raw positive fraction's encoding or denominator. -/
theorem sample_bound (p a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (sample p a b) (radius E T) one := by
  have close : Γ ⊢[PRAAx] le (one*gap a b one one) ((T+one)*b*one) :=
    le_congr (one_mul _).eqSymm (by ipra_ring) (gap_to_one a b T h.andE₂.andE₂)
  have old := GaussianPositiveRationalLogarithmVariation.diagonal_native p a b one one E (T+one) one
    h.andE₁ (.andI (le_refl _) (le_refl _)) (le_refl _) h.andE₂.andE₁
    (le_congr (.eqRefl _) (by ipra_ring) hE) close
  have first : Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample p one one)
      (E*(T+one)*unit p+num 17) (unit p) := distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (one_mul _) old
  have sum := distance_triangle_same _ _ _ _ _ _ (unit_positive p) first (sample_one_bound p)
  have near := distance_radius_mono _ _ _ _ (radius E T) one (unit_positive p) (le_refl one) ?_ sum
  · exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMp near
  · unfold radius
    ipra_le 25*sl (unit_positive (Γ := Γ) p)

def rateInput (a b c d E A D : PTm n) : Fm PTm n := source a b ⋏ (source c d ⋏ (le one D ⋏
  (le b (E*a) ⋏ (le d (E*c) ⋏ distanceBounded (fraction a b) (fraction c d) A D))))
def output (p a b E T : PTm n) : PTm n := pairT (sample p a b) (pairT (radius E T) (fraction a b))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (p a b E T : PTm n) : PTm n := PTm.app outputF ![p,a,b,E,T]
ipra_subst output
theorem program_at (p a b E T : PTm n) : Γ ⊢[PRAAx] run p a b E T ≐ output p a b E T := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,a,b,E,T]
theorem returned_sample (p a b E T : PTm n) : Γ ⊢[PRAAx] fstT (run p a b E T) ≐ sample p a b :=
  (program_at p a b E T).fstE
theorem returned_tail (p a b E T : PTm n) : Γ ⊢[PRAAx] sndT (run p a b E T) ≐ pairT (radius E T) (fraction a b) :=
  (program_at p a b E T).sndE
theorem returned_radius (p a b E T : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p a b E T)) ≐ radius E T :=
  (returned_tail p a b E T).fstE
theorem returned_time (p a b E T : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p a b E T)) ≐ fraction a b :=
  (returned_tail p a b E T).sndE
theorem returned_bound (p a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (fstT (run p a b E T)) (fstT (sndT (run p a b E T))) one :=
  GaussianRationalReciprocal.bound_congr (returned_sample p a b E T).eqSymm (returned_radius p a b E T).eqSymm (.eqRefl _)
    (sample_bound p a b E T hE h)

theorem original_gaussian_positive_time_distance_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 3) ⋏ (le one (var 5) ⋏ distanceBounded
      (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (var 4) (var 5)))) ⟶
      le (var 5*gap (var 0) (var 1) (var 2) (var 3)) (var 4*var 1*var 3)) :=
  closeUniv 6 (.impI (original_gaussian_time_distance _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_gaussian_time_logarithm_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rateInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianNamedInverseRate.independentRate logF logF (data (var 0) (var 1)) (data (var 2) (var 3)) (var 4*var 5) (var 6)) :=
  closeUniv 7 (.impI (original_log_rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem actual_original_compact_logarithm_sample_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ domain (var 1) (var 2) (var 3) (var 4) ⟶ bounded (sample (var 0) (var 1) (var 2)) (radius (var 3) (var 4)) one) :=
  closeUniv 5 (.impI (.impI (sample_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_compact_logarithm_bound_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_compact_logarithm_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ domain (var 1) (var 2) (var 3) (var 4) ⟶
      bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) one) :=
  closeUniv 5 (.impI (.impI (returned_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCompactLogarithmBounds
