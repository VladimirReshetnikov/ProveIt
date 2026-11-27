import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianRealNameExponentialNonnegative
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerRealPowerLowerOrder

/-!
# Nonnegative observations of the unchanged real Euler integrand

The original coefficient, logarithm product and decay point stay on the
real axis at every literal operation clock. The actual exponential
therefore has the nonnegative real lower envelope. This applies at all
positive rational times and to the original fixed-arity evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerRealIntegrandNonnegative

open_ipra
open GaussianEulerIntegrandName (coefficient exponentF exponentData radius nameF data sample)
open GaussianRationalHorner (canonical)
open RationalGaussianEmbedding (axis scalarZero)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z B a b : PTm n) : Fm PTm n := le one B ⋏
  (ZT.eq (ComplexLogarithmRemainder.im z) (ZT.ofNat zero) ⋏ GaussianPositiveRationalLogarithm.source a b)

theorem decay_point_axis (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    axis (GaussianEulerIntegrandName.decayPoint a b) :=
  RationalGaussianEmbedding.axis_congr
    (GaussianEulerDecayRealSamples.fixed_axis_embedding _ (GaussianEulerDecayRealSamples.decay_point_fixed a b hb))
    (RationalGaussianEmbedding.embed_axis _)

theorem exponent_sample_real (p z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    canonical (ap2 exponentF p (exponentData z B a b)) ⋏ axis (ap2 exponentF p (exponentData z B a b)) := by
  have value := GaussianEulerIntegrandName.exponent_at (Γ := Γ) p z B a b
  let I := GaussianEulerIntegrandName.powerClock (GaussianFastValueCut.exponent two p) z B a b
  have axisProduct : Γ ⊢[PRAAx] axis (GaussianRationalHorner.qmul (coefficient z B) (GaussianPositiveRationalLogarithm.sample I a b)) :=
    RationalGaussianEmbedding.axis_multiply _ _
    (GaussianEulerRealPowerLowerOrder.coefficient_axis z B h.andE₁ h.andE₂.andE₁)
    (GaussianPositiveRationalLogarithm.sample_axis I a b)
  exact .andI (GaussianRationalHorner.canonical_congr value (GaussianRationalHorner.qadd_canonical _ _))
    (RationalGaussianEmbedding.axis_congr value.eqSymm
      (RationalGaussianEmbedding.axis_add _ _ axisProduct (decay_point_axis a b h.andE₂.andE₂.andE₂)))

theorem exponent_real_samples (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    GaussianSignedNameExponentialOrder.realSamples exponentF (exponentData z B a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift b) := by
    simpa [source,Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianSignedNameExponentialOrder.realSamples,Syn.shift,GaussianEulerIntegrandName.subst_exponentData] using
    exponent_sample_real (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs

theorem original_name_nonnegative (p z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper scalarZero (fstT (ap2 nameF p (data z B a b))) one (unit p) :=
  GaussianRealNameExponentialNonnegative.original_observation_nonnegative exponentF (radius z B a b) (exponentData z B a b) p
    (GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₁ h.andE₂.andE₂)) (exponent_real_samples z B a b h)

theorem original_integrand_nonnegative (p z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper scalarZero (fstT (sample p z B a b)) one (unit p) :=
  RationalValueBounds.upper_congr (.eqRefl _) (congrFst (GaussianEulerIntegrandName.sample_at p z B a b)).eqSymm
    (.eqRefl _) (.eqRefl _) (original_name_nonnegative p z B a b h)

theorem real_nonnegative_from_margin (z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    zle (ZT.ofNat zero) (ComplexLogarithmRemainder.re z) := by
  let r := ComplexLogarithmRemainder.re z
  let lo := ZT.ofNat B
  let hi := ZT.ofNat A*r
  let g := LeanProofs.IPRA.PTm.monus (hi.pos+lo.neg) (lo.pos+hi.neg)
  have e : ZT.toZ Γ lo+Groth.ι (IPRA.Q.mk Γ g) = ZT.toZ Γ hi := zle_toZ h.andE₂.andE₂
  have mult : Γ ⊢[PRAAx] le (A*r.neg) (A*r.pos) := by
    refine le_of_eq_add (d := B+g) ?_
    apply deriveNat
    simp only [lo,hi,ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    ipra_simps
    linear_combination -e
  have sign := RationalValueBounds.positive_cancel h.andE₁ mult
  apply zle_of_toZ (LeanProofs.IPRA.PTm.monus r.pos r.neg)
  have eq := natEq (eq_add_of_le sign)
  simp only [ZT.ofNat,ZT.toZ]
  dsimp only [r] at eq ⊢
  ipra_simps
  linear_combination -eq

theorem power_source_of_margin (z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hi : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.im z) (ZT.ofNat zero))
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    GaussianEulerRealPowerLowerOrder.source z R B a b :=
  .andI h.andE₂.andE₁ (.andI (.andI (real_nonnegative_from_margin z R B A h) hi) ht)

theorem unchanged_original_real_Euler_integrand_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      RationalValueBounds.upper scalarZero (fstT (sample (var 0) (var 1) (var 2) (var 3) (var 4))) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_integrand_nonnegative _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerRealIntegrandNonnegative
