import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.AnalyticNumberTheory.LogElementary

/-!
# Linear remainder on the original finite harmonic interval

On the original factorial scale, every summand of the interval from
`Q*a` to `Q*(a+c)` lies between the two endpoint rectangles. The
resulting rational interval differs from `c/a` by at most
`c^2/a^2`. All parameters, including the actual mesh, are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicIntervalLinearRemainder

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open Products (fact)
open GammaEulerMesh (factorial_positive factorial_quotient)
open RationalHarmonicInterval (common numerator horizon interval)
open RationalGaussianEmbedding (embed native)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product represents_congr)
open GaussianRationalMetric (distanceBounded qsub)
open ComplexLogarithmRemainder (oneCode scale normSq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem rectangles (a c Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hQ : Γ ⊢[PRAAx] le one Q) (hL : Γ ⊢[PRAAx] le (Q*(a+c)) L) :
    Γ ⊢[PRAAx] (le ((a+c)*S (Q*a) (fact L)+c*fact L) ((a+c)*S (Q*(a+c)) (fact L)) ⋏
      le (a*S (Q*(a+c)) (fact L)) (a*S (Q*a) (fact L)+c*fact L)) := by
  let F := fact L
  let v := Q*a
  let w := Q*c
  let u := Q*(a+c)
  have split : Γ ⊢[PRAAx] v+w ≐ u := by dsimp only [v,w,u]; ipra_ring
  have changeS : Γ ⊢[PRAAx] S (v+w) F ≐ S u F :=
    congrAp2 (sumF hB) split (.eqRefl _)
  have hv : Γ ⊢[PRAAx] le one v := positive_product Q a hQ ha
  have v_le : Γ ⊢[PRAAx] le v (v+w) := le_add_right _ _
  have hV : Γ ⊢[PRAAx] le one (v+w) := le_trans hv v_le
  have hW : Γ ⊢[PRAAx] le (v+w) L := le_congr split.eqSymm (.eqRefl _) hL
  have lower := AnalyticNumberTheory.LogElementary.log_lower v w (factorial_quotient (v+w) L hV hW).eqSymm
  have lowerLeft : Γ ⊢[PRAAx] (v+w)*S v F+F*w ≐ Q*((a+c)*S v F+c*F) :=
    (congrAdd (congrMul split (.eqRefl _)) (.eqRefl _)).eqTrans (by dsimp only [w,u]; ipra_ring)
  have lowerRight : Γ ⊢[PRAAx] (v+w)*S (v+w) F ≐ Q*((a+c)*S u F) :=
    (congrMul split changeS).eqTrans (by dsimp only [u]; ipra_ring)
  have shortLower : Γ ⊢[PRAAx] le (Q*((a+c)*S v F+c*F)) (Q*((a+c)*S u F)) :=
    le_congr lowerLeft lowerRight lower
  have upper := AnalyticNumberTheory.LogElementary.log_upper (Γ := Γ) v w F
  have mono := S_mono F v_le
  have leftRect : Γ ⊢[PRAAx] le (v*S (v+w) F) (v*S v F+w*F) := by
    ipra_le sl upper+sl mono
  have shortUpper : Γ ⊢[PRAAx] le (Q*(a*S u F)) (Q*(a*S v F+c*F)) :=
    le_congr ((congrMul (.eqRefl v) changeS).eqTrans (by dsimp only [v]; ipra_ring))
      (by dsimp only [v,w]; ipra_ring) leftRect
  exact .andI (RationalValueBounds.positive_cancel hQ shortLower) (RationalValueBounds.positive_cancel hQ shortUpper)

theorem common_remainder (a c Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hQ : Γ ⊢[PRAAx] le one Q) (hL : Γ ⊢[PRAAx] le (Q*(a+c)) L) :
    Γ ⊢[PRAAx] distanceBounded (fraction c a) (embed (common (a+c) a Q L)) (c*c) (a*a) := by
  let F := fact L
  let U := S (Q*(a+c)) F
  let V := S (Q*a) F
  let g := monus (a*V+c*F) (a*U)
  let point := embed (common (a+c) a Q L)
  let target := fraction c a
  let v := native (numerator (a+c) a Q L)
  let E := a*F
  have hF := factorial_positive (Γ := Γ) L
  have he := positive_product a F ha hF
  have hAA := positive_product a a ha ha
  have rect := rectangles a c Q L ha hQ hL
  have eq : Γ ⊢[PRAAx] a*U+g ≐ a*V+c*F := (eq_add_of_le rect.andE₂).eqSymm
  have gap : Γ ⊢[PRAAx] le ((a+c)*g) (c*c*F) := by
    have e := natEq eq
    ipra_le 𝔞 a*sl rect.andE₁ using
      try dsimp only [U,V,F] at e ⊢
      try ipra_simps
      linear_combination -(𝔞 a+𝔞 c)*e
  have shorter : Γ ⊢[PRAAx] le (a*g) (c*c*F) :=
    le_trans (mul_le_mul_right g (le_add_right a c)) gap
  have reps := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (common (a+c) a Q L) (numerator (a+c) a Q L) F
    (RationalHarmonicInterval.common_value (a+c) a Q L)
  have source := GaussianRationalHorner.ofGaussian_represents (scale c oneCode) a ha
  have left := GaussianRationalSyntheticDivision.rescale_to target (scale c oneCode) a F E source (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to point v F a E reps (mul_comm _ _)
  have raw := GaussianRationalMetric.qsub_represents _ _ _ _ _ he left right
  have numEq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (scale F (scale c oneCode)) (scale a v)) (scale g oneCode) := by
    apply GaussianRootAlgebra.equal_of_values
    all_goals
      simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,v,
        RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    · have e := natEq eq
      simp only [numerator,ZT.toZ]
      dsimp only [U,V] at e
      ipra_simps
      linear_combination -e
    · ipra_simps
      ring
  have represented := represents_congr (.eqRefl _) numEq (.eqRefl _) raw
  have norm : Γ ⊢[PRAAx] normSq (scale g oneCode) ≐ g*g :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have radius : Γ ⊢[PRAAx] le ((a*a)*g) ((c*c)*E) :=
    le_congr (by ipra_ring) (by dsimp only [E]; ipra_ring) (mul_le_mul_right a shorter)
  change Γ ⊢[PRAAx] distanceBounded target point (c*c) (a*a)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ he hAA represented
  exact le_congr (by
    have e := natEq norm
    apply deriveNat
    ipra_simps
    rw [e]
    ring) (by dsimp only [E]; ipra_ring) (sq_le_sq radius)

theorem interval_remainder (a c Q : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] distanceBounded (fraction c a) (embed (interval (a+c) a Q)) (c*c) (a*a) :=
  common_remainder a c Q (horizon (a+c) a Q) ha hQ (RationalHarmonicInterval.left_horizon _ _ _)

theorem original_harmonic_interval_linear_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ le one (var 2)) ⟶
      distanceBounded (fraction (var 1) (var 0)) (embed (interval (var 0+var 1) (var 0) (var 2)))
        (var 1*var 1) (var 0*var 0)) :=
  closeUniv 3 (.impI (interval_remainder _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianHarmonicIntervalLinearRemainder
