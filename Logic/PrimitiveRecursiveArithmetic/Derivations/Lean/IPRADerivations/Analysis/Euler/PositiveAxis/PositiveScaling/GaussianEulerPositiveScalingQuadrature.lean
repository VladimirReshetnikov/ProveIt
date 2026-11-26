import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingIntegrand
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# The actual finite Euler quadrature under positive rational scaling

The unchanged affine grid on the scaled interval is compared row by row
with the proved actual normalized scaling product. The genuine finite
sum metric and the original compact weight retain the Jacobian c/d and
both independent observation errors. No integral or row-equivalence law
is supplied, and zero interval width is allowed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingQuadrature

open_ipra
open GaussianEulerPositiveScalingIntegrand (productF productData productClock fixedData)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (B a E N c d : PTm n) : Fm PTm n :=
  le one B ⋏ (le one a ⋏ (le one E ⋏ (le one N ⋏ (le one c ⋏ le one d))))
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 productF p
  (productData (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x)))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def sample (p z B a b c d : PTm n) : PTm n := ap3 evaluatorF p (pairT a b) (fixedData z B c d)

ipra_subst source
ipra_subst evaluatorTerm
ipra_subst sample

private theorem product_data_congr (z B a b c d z' B' a' b' c' d' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    productData z B a b c d ≐ productData z' B' a' b' c' d' := by
  have e1 : Γ ⊢[PRAAx] productData z B a b c d ≐ productData z' B a b c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (var 0) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hz
  have e2 : Γ ⊢[PRAAx] productData z' B a b c d ≐ productData z' B' a b c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (Syn.shift z') (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hB
  have e3 : Γ ⊢[PRAAx] productData z' B' a b c d ≐ productData z' B' a' b c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (Syn.shift z') (Syn.shift B') (var 0) (Syn.shift b) (Syn.shift c) (Syn.shift d)) ha
  have e4 : Γ ⊢[PRAAx] productData z' B' a' b c d ≐ productData z' B' a' b' c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (Syn.shift z') (Syn.shift B') (Syn.shift a') (var 0) (Syn.shift c) (Syn.shift d)) hb
  have e5 : Γ ⊢[PRAAx] productData z' B' a' b' c d ≐ productData z' B' a' b' c' d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (Syn.shift z') (Syn.shift B') (Syn.shift a') (Syn.shift b') (var 0) (Syn.shift d)) hc
  have e6 : Γ ⊢[PRAAx] productData z' B' a' b' c' d ≐ productData z' B' a' b' c' d' := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_productData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (productData (Syn.shift z') (Syn.shift B') (Syn.shift a') (Syn.shift b') (Syn.shift c') (var 0)) hd
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans (e4.eqTrans (e5.eqTrans e6))))

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem sample_at (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    sample p z B a b c d ≐ ap2 productF p (productData z B a b c d) := by
  have left := fst_pair (Γ := Γ) (pairT z B) (pairT c d)
  have right := snd_pair (Γ := Γ) (pairT z B) (pairT c d)
  exact (evaluator_at p (pairT a b) (fixedData z B c d)).eqTrans
    (congrAp2 productF (.eqRefl _) (product_data_congr _ _ _ _ _ _ _ _ _ _ _ _
      left.fstE left.sndE
      (fst_pair _ _) (snd_pair _ _)
      right.fstE right.sndE))

theorem sample_readback (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    sample p z B a b c d ≐
      qmul (ap2 powerF (productClock p z B a b c d) (powerData z B c d))
        (GaussianEulerPositiveScalingIntegrand.sample (productClock p z B a b c d) z B a b c d) :=
  (sample_at p z B a b c d).eqTrans (GaussianEulerPositiveScalingIntegrand.product_evaluator_readback p z B a b c d)

theorem grid_source (i B a C E N c d : PTm n) (hs : Γ ⊢[PRAAx] source B a E N c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingIntegrand.source B (a*N+C*i) (E*N) c d := by
  have ha := hs.andE₂.andE₁
  have hn := hs.andE₂.andE₂.andE₂.andE₁
  have hp : Γ ⊢[PRAAx] le one (a*N+C*i) :=
    le_trans (positive_product a N ha hn) (le_add_right _ _)
  exact .andI hs.andE₁ (.andI (.andI hs.andE₂.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂.andE₂)
    (.andI hp (positive_product E N hs.andE₂.andE₂.andE₁ hn)))

theorem row_error (i p q N z B a C E c d : PTm n) (hs : Γ ⊢[PRAAx] source B a E N c d) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i
        (sampleData p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B)))
      (inst2 (sampleBody evaluatorF) i (sampleData q N a C E (fixedData z B c d)))
      (unit p+unit q) (unit p*unit q) := by
  have old := GaussianEulerPositiveScalingIntegrand.original_observations p q z B (a*N+C*i) (E*N) c d
    (grid_source i B a C E N c d hs)
  have left : Γ ⊢[PRAAx]
      inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i
        (sampleData p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B)) ≐
      GaussianEulerIntegrandName.sample p z B (c*(a*N+C*i)) (d*(E*N)) :=
    (sample_body_at GaussianEulerIntegrandName.evaluatorF i p N (c*a) (c*C) (d*E)
      (GaussianEulerIntegrandName.fixedData z B)).eqTrans
    (congrAp3 GaussianEulerIntegrandName.evaluatorF (.eqRefl _) (congrPairT (by ipra_ring) (by ipra_ring)) (.eqRefl _))
  have right := (sample_body_at (Γ := Γ) evaluatorF i q N a C E (fixedData z B c d)).eqTrans (sample_at q z B _ _ c d)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) old

/-- The original scaled quadrature is within the Jacobian times the
width and the two original observation errors of the genuine scaling
product client on the unscaled grid. Both counts remain exactly N. -/
theorem original_quadrature_scaling (p q N z B a C E c d : PTm n)
    (hs : Γ ⊢[PRAAx] source B a E N c d) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B))
      (qmul (fraction c d) (quadrature evaluatorF q N a C E (fixedData z B c d)))
      (c*C*(unit p+unit q)) (d*E*unit p*unit q) := by
  let f := sampleBody GaussianEulerIntegrandName.evaluatorF
  let g := sampleBody evaluatorF
  let x := sampleData p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B)
  let y := sampleData q N a C E (fixedData z B c d)
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift B) (Syn.shift a) (Syn.shift E) (Syn.shift N) (Syn.shift c) (Syn.shift d) :=
    by simpa only [Fm.shift,subst_source,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsDistance f g N x y (unit p+unit q) (unit p*unit q) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,f,g,x,y,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerIntegrandName.subst_fixedData,GaussianEulerPositiveScalingIntegrand.subst_fixedData,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.shift] using
      row_error (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift N) (Syn.shift z) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift c) (Syn.shift d) hh.wk
  have hd := hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have he := hs.andE₂.andE₂.andE₁
  have hn := hs.andE₂.andE₂.andE₂.andE₁
  have de := positive_product d E hd he
  have den : Γ ⊢[PRAAx] le one (unit p*unit q) := positive_product _ _ (unit_positive p) (unit_positive q)
  have finite := sum_distance f g N x y (unit p+unit q) (unit p*unit q) den rows
  have weighted := GaussianRationalReciprocal.bounded_product _ _ (c*C) ((d*E)*N) (N*(unit p+unit q)) (unit p*unit q)
    (positive_product _ _ de hn) den (weight_bound (c*C) (d*E) N de hn) finite
  have difference := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight (c*C) (d*E) N) _ _).eqSymm (.eqRefl _) (.eqRefl _) weighted
  have coarsened : Γ ⊢[PRAAx]
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B))
        (qmul (weight (c*C) (d*E) N) (sum g N y))
        (c*C*(unit p+unit q)) ((d*E)*(unit p*unit q)) := distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ de hn) den) (positive_product _ _ de den)
    (le_of_eq_add (d := zero) (by ipra_ring)) difference
  have factor : Γ ⊢[PRAAx]
      qmul (weight (c*C) (d*E) N) (sum g N y) ≐
        qmul (fraction c d) (quadrature evaluatorF q N a C E (fixedData z B c d)) :=
    (qmul_congr (GaussianRationalQuadratureDilation.weight_factor c d C E N hd he hn).eqSymm (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qmul_associative _ _ _)
  exact distance_congr (.eqRefl _) factor (.eqRefl _) (by ipra_ring) coarsened

/-- The original compact interval source supplies all positivity guards;
the numerical input disk and upper endpoint are not strengthened. -/
theorem original_compact_grid_scaling (p q N z R B a C E T c d : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T)
    (hN : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B))
      (qmul (fraction c d) (quadrature evaluatorF q N a C E (fixedData z B c d)))
      (c*C*(unit p+unit q)) (d*E*unit p*unit q) :=
  original_quadrature_scaling p q N z B a C E c d
    (.andI hs.andE₁.andE₁ (.andI hs.andE₂.andE₁ (.andI hs.andE₁.andE₂.andE₁ (.andI hN (.andI hc hd)))))

theorem actual_original_positive_rational_finite_quadrature_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 4) (var 5) (var 7) (var 2) (var 8) (var 9) ⟶
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 2) (var 8*var 5) (var 8*var 6) (var 9*var 7)
          (GaussianEulerIntegrandName.fixedData (var 3) (var 4)))
        (qmul (fraction (var 8) (var 9)) (quadrature evaluatorF (var 1) (var 2) (var 5) (var 6) (var 7)
          (fixedData (var 3) (var 4) (var 8) (var 9))))
        (var 8*var 6*(unit (var 0)+unit (var 1))) (var 9*var 7*unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_quadrature_scaling _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingQuadrature
