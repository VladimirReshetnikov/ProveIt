import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianUniformFiniteSumBound

/-!
# Finite quadratic substitution with the actual Jacobian client

The corrected density is the original Jacobian client plus
(c/d)*Delta u times the same original mapped row. Its uniform-grid
weight is exactly the nonlinear cell width. A genuine bound M on those
actual mapped observations gives the finite error c*M*C^2/(d*E^2*N).
This does not assume or claim that an arbitrary nonlinear partition is
already equivalent to the original uniform quadrature in the new time.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareJacobian

open_ipra
open GaussianRationalQuadratureSquareCells (source timeMap jacobian cellWidth linearWidth remainder denominator)
open GaussianRationalQuadratureDilation (pullData)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianRationalRiemannRefinement (weight termsDistance sum_distance)
open GaussianUniformFiniteSumBound (summandsBounded summand_bound_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qadd positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pullTerm (F : PR 3) (p t y : PTm n) : PTm n :=
  ap3 F p (timeMap (fstT y) (fstT (sndT y)) t) (sndT (sndT y))
def pullF (F : PR 3) : PR 3 := PTm.toPR (pullTerm F (var 0) (var 1) (var 2))
def jacobianTerm (F : PR 3) (p t y : PTm n) : PTm n :=
  qmul (jacobian (fstT y) (fstT (sndT y)) t) (ap3 (pullF F) p t y)
def jacobianF (F : PR 3) : PR 3 := PTm.toPR (jacobianTerm F (var 0) (var 1) (var 2))
def correctedData (N c d C E x : PTm n) : PTm n := pairT (fraction (c*C) (d*(E*N))) (pullData c d x)
def correctedTerm (F : PR 3) (p t y : PTm n) : PTm n :=
  qadd (ap3 (jacobianF F) p t (sndT y)) (qmul (fstT y) (ap3 (pullF F) p t (sndT y)))
def correctedF (F : PR 3) : PR 3 := PTm.toPR (correctedTerm F (var 0) (var 1) (var 2))
def rowBounds (F : PR 3) (p N c d a C E x M : PTm n) : Fm PTm n :=
  summandsBounded (sampleBody (pullF F)) N (sampleData p N a C E (pullData c d x)) M one

ipra_subst pullTerm
ipra_subst jacobianTerm
ipra_subst correctedData
ipra_subst correctedTerm
ipra_subst rowBounds

theorem pull_at (F : PR 3) (p t c d x : PTm n) : Γ ⊢[PRAAx]
    ap3 (pullF F) p t (pullData c d x) ≐ ap3 F p (timeMap c d t) x := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 2)
    (ap3 F (var 0) (timeMap (var 2) (var 3) (var 1)) (var 4)) p t ![c, d, x]
  simp only [subst_ap3, GaussianRationalQuadratureSquareCells.subst_timeMap, Syn.subst_var] at read
  exact read

theorem jacobian_at (F : PR 3) (p t c d x : PTm n) : Γ ⊢[PRAAx]
    ap3 (jacobianF F) p t (pullData c d x) ≐ qmul (jacobian c d t) (ap3 F p (timeMap c d t) x) := by
  have term : Γ ⊢[PRAAx] ap3 (jacobianF F) p t (pullData c d x) ≐ jacobianTerm F p t (pullData c d x) := by
    simpa [jacobianF,ap3] using toPR_eq (Γ := Γ) (jacobianTerm F (var 0) (var 1) (var 2) : PTm 3) ![p,t,pullData c d x]
  have j : Γ ⊢[PRAAx] jacobian (fstT (pullData c d x)) (fstT (sndT (pullData c d x))) t ≐ jacobian c d t :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
      (congrMul (snd_pair _ _).fstE (.eqRefl _))
  exact term.eqTrans (qmul_congr j (pull_at F p t c d x))

theorem corrected_at (F : PR 3) (p t N c d C E x : PTm n) : Γ ⊢[PRAAx]
    ap3 (correctedF F) p t (correctedData N c d C E x) ≐
      qadd (ap3 (jacobianF F) p t (pullData c d x))
        (qmul (fraction (c*C) (d*(E*N))) (ap3 (pullF F) p t (pullData c d x))) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 1)
    (qadd (ap3 (jacobianF F) (var 0) (var 1) (var 3))
        (qmul (var 2) (ap3 (pullF F) (var 0) (var 1) (var 3)))) p t ![(fraction (c * C) (d * (E * N))), pullData c d x]
  simp only [GaussianRationalHorner.subst_qadd, GaussianRationalHorner.subst_qmul, subst_ap3, Syn.subst_var] at read
  exact read

theorem actual_mapped_row (F : PR 3) (i p N c d a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody (pullF F)) i (sampleData p N a C E (pullData c d x)) ≐ ap3 F p (timeMap c d (grid i N a C E)) x :=
  (sample_body_at (pullF F) i p N a C E _).eqTrans (pull_at F p _ c d x)

theorem weight_correction (N c d C E : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    qmul (weight C E N) (fraction (c*C) (d*(E*N))) ≐ remainder N c d C E :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalQuadratureDilation.weight_factor _ _ C E N
      (positive_product _ _ h.andE₁ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂)) h.andE₂.andE₁ h.andE₂.andE₂).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by unfold denominator; ipra_ring)))

theorem actual_corrected_cell (F : PR 3) (i p N c d a C E x : PTm n) (h : Γ ⊢[PRAAx] source d E N) : Γ ⊢[PRAAx]
    qmul (weight C E N) (ap3 (correctedF F) p (grid i N a C E) (correctedData N c d C E x)) ≐
      qmul (cellWidth i N c d a C E) (ap3 F p (timeMap c d (grid i N a C E)) x) := by
  let w := ap3 F p (timeMap c d (grid i N a C E)) x
  have row := (corrected_at (Γ := Γ) F p (grid i N a C E) N c d C E x).eqTrans
    (qadd_congr (jacobian_at F p _ c d x) (qmul_congr (.eqRefl _) (pull_at F p _ c d x)))
  have left := (qmul_congr (.eqRefl (weight C E N)) row).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add _ _ _)
  have parts := qadd_congr
    ((GaussianReciprocalHorner.qmul_associative _ _ w).eqSymm.eqTrans
      (qmul_congr (GaussianRationalQuadratureSquareCells.actual_linear_weight i N c d a C E h) (.eqRefl _)))
    ((GaussianReciprocalHorner.qmul_associative _ _ w).eqSymm.eqTrans (qmul_congr (weight_correction N c d C E h) (.eqRefl _)))
  have distribute : Γ ⊢[PRAAx] qadd (qmul (linearWidth i N c d a C E) w) (qmul (remainder N c d C E) w) ≐
      qmul (qadd (linearWidth i N c d a C E) (remainder N c d C E)) w :=
    (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add w _ _).eqSymm.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  exact left.eqTrans (parts.eqTrans (distribute.eqTrans
    (qmul_congr (GaussianRationalQuadratureSquareCells.cell_width_split i N c d a C E h).eqSymm (.eqRefl _))))

theorem row_error (F : PR 3) (i p N c d a C E x M : PTm n) (h : Γ ⊢[PRAAx] source d E N)
    (hr : Γ ⊢[PRAAx] rowBounds F p N c d a C E x M) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody (correctedF F)) i (sampleData p N a C E (correctedData N c d C E x)))
      (inst2 (sampleBody (jacobianF F)) i (sampleData p N a C E (pullData c d x)))
      (c*C*M) (d*(E*N)) := by
  have den := positive_product d (E*N) h.andE₁ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂)
  have raw := summand_bound_at (sampleBody (pullF F)) N _ M one i hr hi
  have mapped : Γ ⊢[PRAAx] bounded (ap3 (pullF F) p (grid i N a C E) (pullData c d x)) M one :=
    GaussianRationalReciprocal.bound_congr (sample_body_at (pullF F) i p N a C E _) (.eqRefl _) (.eqRefl _) raw
  have factor : Γ ⊢[PRAAx] bounded (fraction (c*C) (d*(E*N))) (c*C) (d*(E*N)) :=
    GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ den).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded _ _ den)
  have bound := GaussianRationalReciprocal.bounded_product_one_right den factor mapped
  have difference : Γ ⊢[PRAAx] qsub
      (ap3 (correctedF F) p (grid i N a C E) (correctedData N c d C E x))
      (ap3 (jacobianF F) p (grid i N a C E) (pullData c d x)) ≐
      qmul (fraction (c*C) (d*(E*N))) (ap3 (pullF F) p (grid i N a C E) (pullData c d x)) :=
    (qsub_congr (corrected_at F p _ N c d C E x) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.qmul_canonical _ _))
  have point : Γ ⊢[PRAAx] distanceBounded
      (ap3 (correctedF F) p (grid i N a C E) (correctedData N c d C E x))
      (ap3 (jacobianF F) p (grid i N a C E) (pullData c d x)) (c*C*M) (d*(E*N)) :=
    GaussianRationalReciprocal.bound_congr difference.eqSymm (.eqRefl _) (.eqRefl _) bound
  exact distance_congr (sample_body_at (correctedF F) i p N a C E _).eqSymm
    (sample_body_at (jacobianF F) i p N a C E _).eqSymm (.eqRefl _) (.eqRefl _) point

theorem original_finite_jacobian_bound (F : PR 3) (p N c d a C E x M : PTm n)
    (h : Γ ⊢[PRAAx] source d E N) (hr : Γ ⊢[PRAAx] rowBounds F p N c d a C E x M) : Γ ⊢[PRAAx]
    distanceBounded (quadrature (correctedF F) p N a C E (correctedData N c d C E x))
      (quadrature (jacobianF F) p N a C E (pullData c d x)) (c*C*C*M) (d*E*E*N) := by
  let D := d*(E*N)
  have den : Γ ⊢[PRAAx] le one D := positive_product _ _ h.andE₁ (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift d) (Syn.shift E) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] rowBounds F (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d)
      (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody (correctedF F)) (sampleBody (jacobianF F)) N
      (sampleData p N a C E (correctedData N c d C E x)) (sampleData p N a C E (pullData c d x)) (c*C*M) D := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianCompactRiemannName.subst_sampleData,subst_correctedData,
      GaussianRationalQuadratureDilation.subst_pullData,PTm.subst_mul,Syn.shift,D] using
      row_error F (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C)
        (Syn.shift E) (Syn.shift x) (Syn.shift M) hs.wk rs.wk Prf.hyp0
  have sums := sum_distance _ _ _ _ _ _ _ den rows
  have en := positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂
  have bound := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ en den
    (GaussianRationalRiemannRefinement.weight_bound C E N h.andE₂.andE₁ h.andE₂.andE₂) sums
  have distance := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) bound
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en den)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁) h.andE₂.andE₁) h.andE₂.andE₂)
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) distance

theorem actual_finite_quadratic_jacobian_bound_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 3) (var 6) (var 1) ⟶ rowBounds F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (quadrature (correctedF F) (var 0) (var 1) (var 4) (var 5) (var 6)
        (correctedData (var 1) (var 2) (var 3) (var 5) (var 6) (var 7)))
        (quadrature (jacobianF F) (var 0) (var 1) (var 4) (var 5) (var 6) (pullData (var 2) (var 3) (var 7)))
        (var 2*var 5*var 5*var 8) (var 3*var 6*var 6*var 1)) :=
  closeUniv 9 (.impI (.impI (original_finite_jacobian_bound F _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareJacobian
