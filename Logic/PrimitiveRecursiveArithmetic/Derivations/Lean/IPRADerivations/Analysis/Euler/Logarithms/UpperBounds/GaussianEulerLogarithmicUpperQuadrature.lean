import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicUpperScalar
import IPRADerivations.Analysis.Integration.Moments.Decay.GaussianMonomialDecayQuadrature

/-!
# The actual upper logarithmic Euler grid and its left decay observation

All original logarithmic-evaluator rows on an upper-time affine grid
are majorized by the unchanged scalar reference at degree R+j.
The original finite sum, weights and half-decay quadrature therefore
retain exactly the old left-endpoint estimate, with coefficient
2^(R+j+1)*(R+j)!. Mesh and observation errors are unchanged. An
unconditional endpoint uses the actual raw left observation's norm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperQuadrature

open_ipra
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerCompactUpperTail (scalarBody reference_row scaledF scaled_quadrature halfEvaluator)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalRiemannRefinement (termsDistance)
open RationalGaussianRealPart (embedBody)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radius_bounded)
open GaussianEulerUpperTailLeftNorm (numerator denominator errorNumerator original_coefficient)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B E ⋏ (le E a ⋏ le (a+C) (E*T))
def leftObservation (q a E : PTm n) : PTm n := GaussianEulerWeightedHalfDecay.halfSample q a E
def leftNumerator (q a E : PTm n) : PTm n := GaussianL1.norm1 (GaussianRationalL1.rawGaussian (leftObservation q a E))
def leftDenominator (q a E : PTm n) : PTm n := GaussianRationalL1.rawDen (leftObservation q a E)

ipra_subst source

theorem grid_source (i N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicUpperPointwise.source z R B E T (a*N+C*i) (E*N) := by
  let u := a*N+C*i
  let v := E*N
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ h.andE₁.andE₂.andE₁ hN
  have lower : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right N h.andE₂.andE₁) (le_add_right _ _)
  have hlow : Γ ⊢[PRAAx] le v (E*u) := le_trans lower
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right u h.andE₁.andE₂.andE₁))
  have hu : Γ ⊢[PRAAx] le u ((a+C)*N) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_refl (a*N)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) (le_of_lt hi)))
  have top : Γ ⊢[PRAAx] le u (T*v) := le_trans hu
    (le_congr (.eqRefl _) (by dsimp only [v]; ipra_ring) (mul_le_mul_right N h.andE₂.andE₂))
  exact .andI (.andI h.andE₁ (.andI (.andI (le_trans hv lower) hv) (.andI hlow top))) lower

theorem majorized_row (i p N a C E j z R B T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] majorized (inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData j R E T z B)))
      (inst2 scalarBody i (sampleData p N a C E (R+j))) :=
  majorized_congr (sample_body_at evaluatorF i p N a C E (fixedData j R E T z B)).eqSymm
    (GaussianEulerCompactUpperTail.scalar_body_at i p N a C E (R+j)).eqSymm
    (GaussianEulerLogarithmicUpperScalar.original_evaluator_cell_majorized p j z R B E T (a*N+C*i) (E*N)
      (grid_source i N z R B a C E T h hN hi))

theorem original_grid_bound_from_half (p N a C E j z R B T U V : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hV : Γ ⊢[PRAAx] le one V)
    (hHalf : Γ ⊢[PRAAx] bounded (quadrature halfEvaluator p N a C E zero) U V) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N a C E (fixedData j R E T z B))
      ((C*budget (R+j))*V+(majorant (R+j)*U)*(E*unit p)) ((E*unit p)*V) := by
  let x := fixedData j R E T z B
  let d := R+j
  let X := sampleData p N a C E x
  let Y := sampleData p N a C E d
  let M := majorant d
  let Z := sampleData p N a C E M
  have hE := h.andE₁.andE₂.andE₁
  have hm : Γ ⊢[PRAAx] termsMajorized (sampleBody evaluatorF) scalarBody N X Y := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
    have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    simpa only [termsMajorized,X,Y,x,d,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerLogarithmicCompactName.subst_fixedData,PTm.subst_add] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift T) hs.wk ns.wk Prf.hyp0
  have er : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (sampleBody scaledF) N Y Z (budget d) (unit p) := by
    refine .allI (.impI ?_)
    have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    simpa only [termsDistance,Y,Z,M,d,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerWeightedHalfDecay.subst_majorant,GaussianEulerUpperTailScalar.subst_budget,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_add] using
      reference_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift R+Syn.shift j) ns.wk es.wk
  have ref : Γ ⊢[PRAAx] bounded (quadrature scaledF p N a C E M) (M*U) V :=
    bound_congr (scaled_quadrature p N a C E M).eqSymm (.eqRefl _) (one_mul V)
      (bounded_product _ _ M one U V (le_refl one) hV (radius_bounded M one (le_refl one)) hHalf)
  exact GaussianCompactScalarMajorant.compact_majorant_bound evaluatorF scaledF scalarBody
    p p N a C E x Y M (budget d) (unit p) (M*U) V hN hE (unit_positive p) hV hm er ref

/-- The leading factor is exactly the original 2^(R+j+1)*(R+j)!.
The supplied local bound concerns the same actual left decay sample. -/
theorem original_grid_left_norm (p q N a C E j z R B T A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*N))
    (hleft : Γ ⊢[PRAAx] bounded (leftObservation q a E) A D) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N a C E (fixedData j R E T z B))
      (numerator p q N C E (R+j) A D) (denominator p q N E D) := by
  let d := R+j
  let U := GaussianEulerHalfDecayLeftNorm.numerator p q N C E A D
  let V := GaussianEulerHalfDecayLeftNorm.denominator p q N E D
  have hE := h.andE₁.andE₂.andE₁
  have half := GaussianEulerHalfDecayLeftNorm.original_half_decay_left_norm p q N a C E zero A D
    (.andI (le_trans hE h.andE₂.andE₁) (.andI hN (.andI hE (.andI hC (.andI hD hstep))))) hleft
  have hV : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ hD (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q N E hN hE)
  have actual := original_grid_bound_from_half p N a C E j z R B T U V h hN hV half
  have numEq : Γ ⊢[PRAAx] (C*budget d)*V+(majorant d*U)*(E*unit p) ≐ numerator p q N C E d A D := by
    have coeff := natEq (original_coefficient (Γ := Γ) d)
    apply deriveNat
    dsimp only [U,V,numerator,errorNumerator,GaussianEulerHalfDecayLeftNorm.numerator,GaussianEulerHalfDecayLeftNorm.denominator]
    ipra_simps
    rw [coeff]
    ring
  exact bound_congr (.eqRefl _) numEq (by dsimp only [V,denominator,GaussianEulerHalfDecayLeftNorm.denominator]; ipra_ring) actual

theorem raw_observation_bound (q : PTm n) : Γ ⊢[PRAAx]
    bounded q (GaussianL1.norm1 (GaussianRationalL1.rawGaussian q)) (GaussianRationalL1.rawDen q) := by
  let g := GaussianRationalL1.rawGaussian q
  let D := GaussianRationalL1.rawDen q
  have hd : Γ ⊢[PRAAx] le one D := GaussianRationalL1.raw_den_positive q
  have native : Γ ⊢[PRAAx] le ((D*D)*ComplexLogarithmRemainder.normSq g)
      ((GaussianL1.norm1 g*GaussianL1.norm1 g)*(D*D)) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (mul_le_mul_right (D*D) (GaussianL1.normSq_le_norm1_square g))
  exact GaussianRationalMetric.bounded_of_cleared q g D (GaussianL1.norm1 g) D hd hd
    (GaussianRationalL1.raw_represents q) native

/-- No bound on a returned name or integrand is supplied: the exact
actual left observation itself determines the retained endpoint radius. -/
theorem original_actual_left_endpoint (p q N a C E j z R B T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N a C E (fixedData j R E T z B))
      (numerator p q N C E (R+j) (leftNumerator q a E) (leftDenominator q a E))
      (denominator p q N E (leftDenominator q a E)) :=
  original_grid_left_norm p q N a C E j z R B T _ _ h hN hC (GaussianRationalL1.raw_den_positive _) hstep
    (raw_observation_bound (leftObservation q a E))

theorem actual_logarithmic_upper_grid_retains_left_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 7) (var 8) (var 9) (var 3) (var 4) (var 5) (var 10) ⋏
      le one (var 2) ⋏ le one (var 4) ⋏ le (var 4) ((two*var 5)*var 2)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 2) (var 3) (var 4) (var 5)
        (fixedData (var 6) (var 8) (var 5) (var 10) (var 7) (var 9)))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 5) (var 8+var 6)
          (leftNumerator (var 1) (var 3) (var 5)) (leftDenominator (var 1) (var 3) (var 5)))
        (denominator (var 0) (var 1) (var 2) (var 5) (leftDenominator (var 1) (var 3) (var 5)))) :=
  closeUniv 11 (.impI (original_actual_left_endpoint _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperQuadrature
