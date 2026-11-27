import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLinearStep
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayMesh

/-!
# The actual beta primitive telescope on the original compact grid

Every endpoint retains the original power observation at its actual
argument-dependent product clock. Each row is the unchanged beta-grid
row. A genuine finite telescope and the original finite-sum metric
estimate aggregate a local first-order cell bound. The weighted sum is
exactly the original beta quadrature divided by its numerical degree.
The local analytic cell bound is explicit; no integral identity, output
name law, or supplied finite telescope is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveGridTelescope

open_ipra
open GaussianRationalHorner (qzero qadd qmul positive_product ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique represents_congr)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalFiniteSum (sum sum_zero sum_succ)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianBetaKernelGridComparison (sampleDataBeta row)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def endpoint (p z B a b N : PTm n) : PTm n :=
  GaussianBetaPrimitiveLinearStep.sample (GaussianEulerCompactProductComparison.clock p z B a b) z B a b N
ipra_subst endpoint [GaussianBetaPrimitiveLinearStep.sample, GaussianBetaPrimitiveLinearStep.argument, GaussianEulerPowerIncrement.point, GaussianTimeWeightedPolynomialIncrement.value]
def endpointTerm (p t x : PTm n) : PTm n := endpoint p (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (sndT x)
def endpointF : PR 3 := PTm.toPR (endpointTerm (var 0) (var 1) (var 2))

theorem endpoint_at (p z B a b N : PTm n) : Γ ⊢[PRAAx]
    ap3 endpointF p (pairT a b) (sampleDataBeta z B N) ≐ endpoint p z B a b N := by
  have read := toPR_pairVector3_eq (Γ := Γ)
    (endpoint (var 0) (fstT (var 2)) (sndT (var 2)) (fstT (var 1)) (sndT (var 1)) (var 3) : PTm 4) p (pairT a b) ![pairT z B, N]
  simp only [subst_endpoint,
    subst_fstT, subst_sndT, Syn.subst_var] at read
  refine read.eqTrans ?_
  ipra_congr (endpoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p, fst_pair z B, snd_pair z B, fst_pair a b, snd_pair a b, .eqRefl N]

def gridEndpoint (i p z B a C E M N : PTm n) : PTm n := endpoint p z B (a*M+C*i) (E*M) N
def gridRow (i p z B a C E M N : PTm n) : PTm n := row p z B (a*M+C*i) (E*M) N
def step (C E M N : PTm n) : PTm n := fraction C ((E*M)*N)
def quadratureScaled (p z B a C E M N : PTm n) : PTm n :=
  qmul (fraction one N) (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (sampleDataBeta z B N))
def cellNumerator (p C E M K Z : PTm n) : PTm n := K*C*C*unit p+LeanProofs.IPRA.PTm.num 6*Z*(E*M)*(E*M)
def cellDenominator (p E M : PTm n) : PTm n := (E*M)*(E*M)*unit p
def globalDenominator (p E M : PTm n) : PTm n := E*E*M*unit p

ipra_subst gridEndpoint
ipra_subst gridRow
ipra_subst step
ipra_subst cellNumerator
ipra_subst cellDenominator

theorem endpoint_grid_at (i p z B a C E M N : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody endpointF) i (sampleData p M a C E (sampleDataBeta z B N)) ≐ gridEndpoint i p z B a C E M N :=
  (sample_body_at endpointF i p M a C E (sampleDataBeta z B N)).eqTrans (endpoint_at p z B (a*M+C*i) (E*M) N)
theorem row_grid_at (i p z B a C E M N : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody GaussianBetaKernelGridComparison.evaluatorF) i (sampleData p M a C E (sampleDataBeta z B N)) ≐ gridRow i p z B a C E M N :=
  (sample_body_at _ i p M a C E (sampleDataBeta z B N)).eqTrans (GaussianBetaKernelGridComparison.row_at p z B (a*M+C*i) (E*M) N)

theorem weighted_grid_at (i p z B a C E M N : PTm n) : Γ ⊢[PRAAx]
    inst2 (GaussianRationalFiniteSum.multiplyBody (sampleBody GaussianBetaKernelGridComparison.evaluatorF)) i
      (pairT (step C E M N) (sampleData p M a C E (sampleDataBeta z B N))) ≐
        qmul (gridRow i p z B a C E M N) (step C E M N) :=
  (GaussianRationalFiniteSum.multiply_body_at _ (step C E M N) i (sampleData p M a C E (sampleDataBeta z B N))).eqTrans
    ((qmul_congr (.eqRefl _) (row_grid_at i p z B a C E M N)).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))

private def forwardDifference (f : PTm 2) : PTm 2 := qsub (inst2 f (succ (var 0)) (var 1)) (inst2 f (var 0) (var 1))
@[simp] private theorem forward_at (f : PTm 2) (i x : PTm n) :
    inst2 (forwardDifference f) i x = qsub (inst2 f (succ i) x) (inst2 f i x) := by
  change Syn.subst ![i,x] (forwardDifference f) = _
  simp only [forwardDifference,GaussianRationalMetric.subst_qsub,subst_inst2,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
private def forwardLaw (f : PTm 2) (x k : PTm n) : Fm PTm n :=
  sum (forwardDifference f) k x ≐ qsub (inst2 f k x) (inst2 f zero x)
@[simp] private theorem subst_forwardLaw {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x k : PTm n) :
    (forwardLaw f x k).subst σ = forwardLaw f (Syn.subst σ x) (Syn.subst σ k) := by simp [forwardLaw]

private theorem forward_telescope (f : PTm 2) (x k : PTm n) : Γ ⊢[PRAAx]
    sum (forwardDifference f) k x ≐ qsub (inst2 f k x) (inst2 f zero x) := by
  have all : Γ ⊢[PRAAx] .all (forwardLaw f (Syn.shift x) (var 0)) := by
    ipra_qfind [subst_forwardLaw]
    · exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self _).eqSymm
    · refine (GaussianRationalFiniteSum.sum_succ (forwardDifference f) _ _).eqTrans ?_
      rw [forward_at]
      exact (qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
          (GaussianReconstructionRoots.difference_chain _ _ _))
  have result : Γ ⊢[PRAAx] forwardLaw f x k := by
    simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact result

/-- Exact telescope of the actual original endpoint codes, including
all argument-dependent precision changes and the empty grid. -/
theorem grid_telescope (p z B a C E M N : PTm n) : Γ ⊢[PRAAx]
    sum (forwardDifference (sampleBody endpointF)) M (sampleData p M a C E (sampleDataBeta z B N)) ≐
      qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N) :=
  (forward_telescope _ _ _).eqTrans (qsub_congr (endpoint_grid_at _ _ _ _ _ _ _ _ _) (endpoint_grid_at _ _ _ _ _ _ _ _ _))

private theorem weight_identity (C E M N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (fraction one N) (GaussianRationalRiemannRefinement.weight C E M) ≐ step C E M N := by
  let D := E*M
  have hd := positive_product E M hE hM
  have prod := GaussianRationalHorner.qmul_represents (Γ := Γ) (fraction one N) (GaussianRationalRiemannRefinement.weight C E M)
    (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode)
    (ComplexLogarithmRemainder.scale C ComplexLogarithmRemainder.oneCode) N D hN hd
    (ofGaussian_represents _ _ hN) (ofGaussian_represents _ _ hd)
  apply canonical_unique _ _ (ComplexLogarithmRemainder.scale C ComplexLogarithmRemainder.oneCode) (N*D)
    (GaussianRationalHorner.qmul_canonical _ _) (ofGaussian_canonical _ _ (positive_product D N hd hN)) (positive_product N D hN hd)
    (hrv := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm D N) (ofGaussian_represents _ _ (positive_product D N hd hN)))
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := prod)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

theorem scaled_quadrature_sum (p z B a C E M N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    quadratureScaled p z B a C E M N ≐
      qmul (step C E M N) (sum (sampleBody GaussianBetaKernelGridComparison.evaluatorF) M (sampleData p M a C E (sampleDataBeta z B N))) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    (qmul_congr (weight_identity C E M N hE hM hN) (.eqRefl _))

/-- This is the explicit local first-order cell contract. Every value is
an actual original row or endpoint at its actual requested clock. -/
def cellBound (p z B a C E M N K Z : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift M) ⟶ distanceBounded
    (qsub (gridEndpoint (succ (var 0)) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N))
      (gridEndpoint (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N)))
    (qmul (gridRow (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N)) (step (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N)))
    (cellNumerator (Syn.shift p) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift K) (Syn.shift Z)) (cellDenominator (Syn.shift p) (Syn.shift E) (Syn.shift M)))
ipra_subst cellBound [Syn.subst_shift, Syn.shift_subst]

theorem cell_at (i p z B a C E M N K Z : PTm n) (h : Γ ⊢[PRAAx] cellBound p z B a C E M N K Z)
    (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    distanceBounded (qsub (gridEndpoint (succ i) p z B a C E M N) (gridEndpoint i p z B a C E M N))
      (qmul (gridRow i p z B a C E M N) (step C E M N)) (cellNumerator p C E M K Z) (cellDenominator p E M) := by
  have rule := h.allE i
  simp only [cellBound,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,GaussianRationalMetric.subst_qsub,
    subst_gridEndpoint,GaussianRationalHorner.subst_qmul,subst_gridRow,subst_step,subst_cellNumerator,subst_cellDenominator,
    Syn.subst_var,ConciseIPRA.PTm.subst_succ,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hi

theorem aggregate (p z B a C E M N K Z : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hCells : Γ ⊢[PRAAx] cellBound p z B a C E M N K Z) : Γ ⊢[PRAAx]
    distanceBounded (qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N))
      (quadratureScaled p z B a C E M N) (cellNumerator p C E M K Z) (globalDenominator p E M) := by
  let f := sampleBody endpointF
  let g := sampleBody GaussianBetaKernelGridComparison.evaluatorF
  let x := sampleData p M a C E (sampleDataBeta z B N)
  let w := step C E M N
  have rows : Γ ⊢[PRAAx] termsDistance (forwardDifference f) (GaussianRationalFiniteSum.multiplyBody g) M x (pairT w x)
      (cellNumerator p C E M K Z) (cellDenominator p E M) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] cellBound (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N) (Syn.shift K) (Syn.shift Z) := by simpa [Fm.shift,Syn.shift] using hCells.shift
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
    have actual := cell_at (Γ := Δ) (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N) (Syn.shift K) (Syn.shift Z) hs.wk Prf.hyp0
    have left := qsub_congr (endpoint_grid_at (Γ := Δ) (succ (var 0)) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N))
      (endpoint_grid_at (Γ := Δ) (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N))
    have right := weighted_grid_at (Γ := Δ) (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift N)
    simpa only [termsDistance,forward_at,Δ,f,g,x,w,Syn.shift,GaussianBetaKernelGridComparison.subst_sampleDataBeta,GaussianCompactRiemannName.subst_sampleData,subst_step,subst_pairT,subst_cellNumerator,subst_cellDenominator] using
      distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) actual
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product E M hE hM) (positive_product E M hE hM)) (unit_positive p)
  have raw : Γ ⊢[PRAAx] distanceBounded (sum (forwardDifference f) M x)
      (sum (GaussianRationalFiniteSum.multiplyBody g) M (pairT w x)) (M*cellNumerator p C E M K Z) (cellDenominator p E M) :=
    sum_distance (forwardDifference f) (GaussianRationalFiniteSum.multiplyBody g) M x (pairT w x)
      (cellNumerator p C E M K Z) (cellDenominator p E M) hd rows
  have actual := distance_congr (grid_telescope p z B a C E M N)
    ((GaussianRationalFiniteSum.sum_multiply g w M x).eqTrans (scaled_quadrature_sum p z B a C E M N hE hM hN).eqSymm) (.eqRefl _) (.eqRefl _) raw
  have finalDen := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product E E hE hE) hM) (unit_positive p)
  exact distance_radius_mono _ _ _ _ _ _ hd finalDen
    (le_of_eq_add (d := zero) (by dsimp only [cellDenominator,globalDenominator]; ipra_ring)) actual

ipra_subst quadratureScaled

/-- Actual original endpoint difference, scaled original quadrature,
and unchanged original quadrature, returned by one actual program. -/
def output (p z B a C E M N : PTm n) : PTm n :=
  pairT (qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N))
    (pairT (quadratureScaled p z B a C E M N)
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (sampleDataBeta z B N)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p z B a C E M N : PTm n) : PTm n := PTm.app outputF ![p,z,B,a,C,E,M,N]
theorem program_at (p z B a C E M N : PTm n) : Γ ⊢[PRAAx] run p z B a C E M N ≐ output p z B a C E M N := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,z,B,a,C,E,M,N]

theorem actual_original_beta_grid_endpoint_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (sum (forwardDifference (sampleBody endpointF)) (var 6) (sampleData (var 0) (var 6) (var 3) (var 4) (var 5) (sampleDataBeta (var 1) (var 2) (var 7))) ≐
      qsub (gridEndpoint (var 6) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (gridEndpoint zero (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (grid_telescope _ _ _ _ _ _ _ _)
theorem actual_original_beta_scaled_quadrature_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 5) ⋏ le one (var 6) ⋏ le one (var 7)) ⟶
      quadratureScaled (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
        qmul (step (var 4) (var 5) (var 6) (var 7))
          (sum (sampleBody GaussianBetaKernelGridComparison.evaluatorF) (var 6)
            (sampleData (var 0) (var 6) (var 3) (var 4) (var 5) (sampleDataBeta (var 1) (var 2) (var 7))))) :=
  closeUniv 8 (.impI (scaled_quadrature_sum _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_original_beta_finite_telescope_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((le one (var 5) ⋏ le one (var 6) ⋏ le one (var 7) ⋏ cellBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) ⟶
      distanceBounded
        (qsub (gridEndpoint (var 6) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (gridEndpoint zero (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (quadratureScaled (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (cellNumerator (var 0) (var 4) (var 5) (var 6) (var 8) (var 9)) (globalDenominator (var 0) (var 5) (var 6))) :=
  closeUniv 10 (.impI (aggregate _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_original_beta_grid_telescope_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveGridTelescope
