import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianUpperTimeLogarithmBound
import IPRADerivations.AnalyticNumberTheory.LogElementary

/-!
# Actual positive time for the substitution u = exp(-t)

For the original rational unit-interval input u=a/b, the actual harmonic
logarithm of b/a is written as an explicitly evaluated positive fraction.
The old finite rectangle bound gives its lower margin 1/b at EVERY
observation, and the old upper rectangle gives the uniform upper bound b.
Thus the next original logarithm may be evaluated on these actual samples;
no logarithm of a named value or inverse-chart law is assumed here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicMargin

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open RationalHarmonicInterval (horizon)
open GaussianRationalHorner (represents represents_congr positive_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianHarmonicLogarithmName (clock)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (a b : PTm n) : Fm PTm n := le one a ⋏ lt a b
def mesh (p : PTm n) : PTm n := GammaEulerConstantName.mesh (clock p)
def denominator (p a b : PTm n) : PTm n := fact (horizon b a (mesh p))
def numerator (p a b : PTm n) : PTm n :=
  monus (S (mesh p*b) (denominator p a b)) (S (mesh p*a) (denominator p a b))
def timeF : PR 2 := GaussianHarmonicLogarithmName.nameF
def timeData (a b : PTm n) : PTm n := GaussianHarmonicLogarithmName.data b a

ipra_subst source
ipra_subst mesh [GammaEulerConstantName.mesh, GammaEulerConstantName.unit]
ipra_subst denominator
ipra_subst numerator [S]
ipra_subst timeData

theorem denominator_positive (p a b : PTm n) : Γ ⊢[PRAAx] le one (denominator p a b) := GammaEulerMesh.factorial_positive _

alias gap_positive := Common.one_le_monus_of_lt

/-- The original factorial harmonic numerator satisfies the exact lower
rectangle bound; only the actual mesh is canceled. -/
theorem finite_margin (a b Q : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    le (monus b a*fact (horizon b a Q))
      (b*monus (S (Q*b) (fact (horizon b a Q))) (S (Q*a) (fact (horizon b a Q)))) := by
  let F := fact (horizon b a Q)
  let u := Q*b
  let v := Q*a
  let g := monus b a
  let d := monus (S u F) (S v F)
  have vu : Γ ⊢[PRAAx] le v u := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q hab)
  have hu := positive_product _ _ hQ (le_trans ha hab)
  have endpoint : Γ ⊢[PRAAx] v+Q*g ≐ u :=
    (by dsimp only [v,g]; ipra_ring : Γ ⊢[PRAAx] v+Q*g ≐ Q*(a+monus b a)).eqTrans
      (congrMul (.eqRefl Q) (eq_add_of_le hab).eqSymm)
  have div := GammaEulerMesh.factorial_quotient u (horizon b a Q) hu (RationalHarmonicInterval.left_horizon b a Q)
  have factor : Γ ⊢[PRAAx] F ≐ (v+Q*g)*quo F u := div.eqSymm.eqTrans (congrMul endpoint.eqSymm (.eqRefl _))
  have lower := AnalyticNumberTheory.LogElementary.log_lower v (Q*g) factor
  have lower' : Γ ⊢[PRAAx] le (u*S v F+F*(Q*g)) (u*S u F) :=
    le_congr (congrAdd (congrMul endpoint (.eqRefl _)) (.eqRefl _))
      (congrMul endpoint (congrAp2 (sumF hB) endpoint (.eqRefl F))) lower
  have clear : Γ ⊢[PRAAx] le (F*(Q*g)) (u*d) := by
    dsimp only [d]
    ipra_le sl lower' with 𝔞(u)*natEq (eq_add_of_le (AnalyticNumberTheory.HarmonicChebyshev.S_mono F vu))
  exact RationalValueBounds.positive_cancel hQ
    (le_congr (by ipra_ring) (by dsimp only [u]; ipra_ring) clear)

private theorem numerator_represents (p a b : PTm n) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    represents (ap2 timeF p (timeData a b))
      (ComplexLogarithmRemainder.scale (numerator p a b) ComplexLogarithmRemainder.oneCode) (denominator p a b) := by
  let Q := mesh p
  let L := horizon b a Q
  let F := fact L
  let u := Q*b
  let v := Q*a
  let d := monus (S u F) (S v F)
  have vu : Γ ⊢[PRAAx] le v u := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q hab)
  have equation := natEq (eq_add_of_le (AnalyticNumberTheory.HarmonicChebyshev.S_mono F vu))
  have old := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (RationalHarmonicInterval.interval b a Q)
    (RationalHarmonicInterval.numerator b a Q L) F (RationalHarmonicInterval.common_value b a Q L)
  have rep : Γ ⊢[PRAAx] represents (RationalGaussianEmbedding.embed (RationalHarmonicInterval.interval b a Q))
      (ComplexLogarithmRemainder.scale d ComplexLogarithmRemainder.oneCode) F := by
    apply represents_congr (.eqRefl _) ?_ (.eqRefl _) old
    apply GaussianRootAlgebra.equal_of_values
    · simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
      simp only [RationalHarmonicInterval.numerator,ZT.toZ]
      dsimp only [d,u,v,F,L,Q] at equation ⊢
      ipra_simps
      linear_combination equation
    · simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_im_code,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
      ipra_simps
      ring
  exact GaussianRationalHorner.represents_congr (GaussianHarmonicLogarithmName.sample_at p b a).eqSymm
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _) rep

theorem actual_time_fraction (p a b : PTm n) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    ap2 timeF p (timeData a b) ≐ fraction (numerator p a b) (denominator p a b) :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianHarmonicLogarithmName.sample_real p b a).andE₁
    (GaussianRationalHorner.ofGaussian_canonical _ _ (denominator_positive p a b)) (denominator_positive p a b)
    (numerator_represents p a b hab) (GaussianRationalHorner.ofGaussian_represents _ _ (denominator_positive p a b))

theorem numerator_margin (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    le (denominator p a b) (b*numerator p a b) :=
  le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (denominator p a b) (gap_positive a b h.andE₂)))
    (finite_margin a b (mesh p) h.andE₁ (le_of_lt h.andE₂) (GammaEulerConstantName.mesh_positive _))

theorem numerator_positive (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] le one (numerator p a b) := by
  have bound := le_trans (denominator_positive p a b) (numerator_margin p a b h)
  refine .orE (zero_or_succ (numerator p a b)) ?_ ?_
  · have e : (numerator p a b ≐ zero)::Γ ⊢[PRAAx] b*numerator p a b ≐ zero :=
      (congrMul (.eqRefl b) Prf.hyp0).eqTrans (mul_zero b)
    have bad : (numerator p a b ≐ zero)::Γ ⊢[PRAAx] le one zero := le_congr (.eqRefl _) e bound.wk
    exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred (numerator p a b)))

theorem numerator_upper (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    le (numerator p a b) (b*denominator p a b) := by
  let Q := mesh p
  let F := denominator p a b
  let u := Q*b
  let v := Q*a
  let d := monus (S u F) (S v F)
  have hQ : Γ ⊢[PRAAx] le one Q := GammaEulerConstantName.mesh_positive (clock p)
  have vu : Γ ⊢[PRAAx] le v u := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q (le_of_lt h.andE₂))
  have increment := RationalHarmonicIntervalVariation.harmonic_increment u v F vu
  have weak := le_trans increment (add_le_add₂ (le_refl (v*S v F))
    (mul_le_mul_right F (GaussianRationalMonicReconstruction.monus_le_left u v)))
  have delta : Γ ⊢[PRAAx] le (v*d) (u*F) := by
    dsimp only [d]
    ipra_le sl weak with 𝔞(v)*natEq (eq_add_of_le (AnalyticNumberTheory.HarmonicChebyshev.S_mono F vu))
  have clear : Γ ⊢[PRAAx] le (a*d) (b*F) := RationalValueBounds.positive_cancel hQ
    (le_congr (by dsimp only [u,v]; ipra_ring) (by dsimp only [u,v]; ipra_ring) delta)
  exact le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right d h.andE₁)) clear

/-- Every ACTUAL harmonic observation is already an admissible positive
rational input for the original outer logarithm, on one fixed compact. -/
theorem evaluated_time_domain (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (numerator p a b) (denominator p a b) b b :=
  .andI (.andI (numerator_positive p a b h) (denominator_positive p a b))
    (.andI (numerator_margin p a b h) (numerator_upper p a b h))

theorem time_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN timeF (timeData a b) :=
  GaussianHarmonicLogarithmName.name_regular b a (.andI (le_trans h.andE₁ (le_of_lt h.andE₂)) h.andE₁)

theorem actual_unit_logarithmic_time_positive_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶
      ((le one (numerator (var 0) (var 1) (var 2)) ⋏ le (denominator (var 0) (var 1) (var 2)) (var 2*numerator (var 0) (var 1) (var 2))) ⋏
        ap2 timeF (var 0) (timeData (var 1) (var 2)) ≐ fraction (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (.andI (numerator_positive _ _ _ Prf.hyp0) (numerator_margin _ _ _ Prf.hyp0))
    (actual_time_fraction _ _ _ (le_of_lt Prf.hyp0.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicMargin
