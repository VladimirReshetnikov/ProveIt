import IPRADerivations.Analysis.Euler.Integration.Parts.Grids.GaussianEulerIntegrationByPartsGridObservation
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsStep

/-!
# Actual finite Euler integration-by-parts telescope

The actual original boundary values are telescoped on the literal
affine grid. Every local analytic source follows from the native compact
and mesh guards. The actual weighted operator quadrature has the exact
finite error K*C²/(E²*N) plus N times the original sampling allowance.
Endpoint encodings are retained; no endpoint rescaling or integral law
is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGrid

open_ipra
open GaussianEulerIntegrationByPartsLinear (primitive originalProduct cell)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrandName (fixedData)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def operator (p z B a b : PTm n) : PTm n := qmul (originalProduct p z B a b)
  (qsub (GaussianRationalHorner.ofGaussian z B) (GaussianPositiveRationalLogarithm.fraction a b))
def operatorTerm (p t x : PTm n) : PTm n := operator p (fstT x) (sndT x) (fstT t) (sndT t)
def operatorF : PR 3 := PTm.toPR (operatorTerm (var 0) (var 1) (var 2))
def endpointTerm (p t x : PTm n) : PTm n := primitive p (fstT x) (sndT x) (fstT t) (sndT t)
def endpointF : PR 3 := PTm.toPR (endpointTerm (var 0) (var 1) (var 2))
def endpoint (i p z B a C E N : PTm n) : PTm n := primitive p z B (a*N+C*i) (E*N)
def source (z R B a C E T N : PTm n) : Fm PTm n := intervalSource z R B a C E T ⋏
  (le one N ⋏ (le one C ⋏ (le ((R+one)*C) (a*N) ⋏ le C (E*N))))
def numerator (p R E T C N : PTm n) : PTm n := GaussianEulerIntegrationByPartsStep.curvature R E T*C*C*unit p+
  T*GaussianEulerIntegrationByPartsProductStep.observationCost R E T*(E*E*N*N)
def denominator (p E N : PTm n) : PTm n := E*E*N*unit p

ipra_subst operator
ipra_subst operatorTerm
ipra_subst endpointTerm
ipra_subst endpoint
ipra_subst source

theorem operator_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap3 operatorF p (pairT a b) (fixedData z B) ≐ operator p z B a b := by
  have program : Γ ⊢[PRAAx] ap3 operatorF p (pairT a b) (fixedData z B) ≐ operatorTerm p (pairT a b) (fixedData z B) :=
    by simpa [operatorF,ap3] using toPR_eq (Γ := Γ) (operatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,fixedData z B]
  apply program.eqTrans
  ipra_congr (operator (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (fixedData z B) ≐ z from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (fixedData z B) ≐ B from snd_pair _ _),
      (show _ ⊢[PRAAx] fstT (pairT a b) ≐ a from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (pairT a b) ≐ b from snd_pair _ _)] using [operatorTerm]

theorem endpoint_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap3 endpointF p (pairT a b) (fixedData z B) ≐ primitive p z B a b := by
  have program : Γ ⊢[PRAAx] ap3 endpointF p (pairT a b) (fixedData z B) ≐ endpointTerm p (pairT a b) (fixedData z B) :=
    by simpa [endpointF,ap3] using toPR_eq (Γ := Γ) (endpointTerm (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,fixedData z B]
  apply program.eqTrans
  ipra_congr (primitive (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (fixedData z B) ≐ z from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (fixedData z B) ≐ B from snd_pair _ _),
      (show _ ⊢[PRAAx] fstT (pairT a b) ≐ a from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (pairT a b) ≐ b from snd_pair _ _)] using [endpointTerm]

theorem endpoint_grid_at (i p z B a C E N : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody endpointF) i (sampleData p N a C E (fixedData z B)) ≐ endpoint i p z B a C E N :=
  (sample_body_at endpointF i p N a C E _).eqTrans (endpoint_at p z B (a*N+C*i) (E*N))

theorem primitive_numerator_congr (p z B a a' b : PTm n) (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    primitive p z B a b ≐ primitive p z B a' b := by
  ipra_congr (primitive (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl p, .eqRefl z, .eqRefl B, h, .eqRefl b]

private def forward (f : PTm 2) : PTm 2 := qsub (inst2 f (succ (var 0)) (var 1)) (inst2 f (var 0) (var 1))
@[simp] private theorem forward_at (f : PTm 2) (i x : PTm n) :
    inst2 (forward f) i x = qsub (inst2 f (succ i) x) (inst2 f i x) := by
  change Syn.subst ![i,x] (forward f) = _
  simp only [forward,GaussianRationalMetric.subst_qsub,subst_inst2,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
private def forwardLaw (f : PTm 2) (x k : PTm n) : Fm PTm n := sum (forward f) k x ≐ qsub (inst2 f k x) (inst2 f zero x)
@[simp] private theorem subst_forwardLaw {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x k : PTm n) :
    (forwardLaw f x k).subst σ = forwardLaw f (Syn.subst σ x) (Syn.subst σ k) := by simp [forwardLaw]

private theorem forward_sum (f : PTm 2) (x k : PTm n) : Γ ⊢[PRAAx]
    sum (forward f) k x ≐ qsub (inst2 f k x) (inst2 f zero x) := by
  have all : Γ ⊢[PRAAx] .all (forwardLaw f (Syn.shift x) (var 0)) := by
    ipra_qfind [subst_forwardLaw]
    · exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self _).eqSymm
    · refine (GaussianRationalFiniteSum.sum_succ (forward f) _ _).eqTrans ?_
      rw [forward_at]
      exact (qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianReconstructionRoots.difference_chain _ _ _))
  have result : Γ ⊢[PRAAx] forwardLaw f x k := by
    simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact result

theorem grid_telescope (p z B a C E N : PTm n) : Γ ⊢[PRAAx]
    sum (forward (sampleBody endpointF)) N (sampleData p N a C E (fixedData z B)) ≐
      qsub (endpoint N p z B a C E N) (endpoint zero p z B a C E N) :=
  (forward_sum _ _ _).eqTrans (qsub_congr (endpoint_grid_at _ _ _ _ _ _ _ _) (endpoint_grid_at _ _ _ _ _ _ _ _))

theorem cell_source (i z R B a C E T N : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsProductStep.source z R B E T (a*N+C*i) (E*N) C := by
  have here := GaussianEulerIntegrationByPartsGridObservation.grid_source i N z R B a C E T h.andE₁ h.andE₂.andE₁ (le_of_lt hi)
  have later := GaussianEulerIntegrationByPartsGridObservation.grid_source (succ i) N z R B a C E T h.andE₁ h.andE₂.andE₁ hi
  have upper : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (a*N+C*i+C) (E*N) E T := by
    have eq : Γ ⊢[PRAAx] a*N+C*succ i ≐ a*N+C*i+C := by ipra_ring
    simpa only [GaussianCompactLogarithmBounds.subst_domain,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (GaussianCompactLogarithmBounds.domain (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
        ![a*N+C*succ i,E*N,E,T] ![a*N+C*i+C,E*N,E,T]
        (fun j => by fin_cases j; exact eq; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _) (by simpa using later.andE₂)
  exact .andI (.andI here.andE₁ (.andI here.andE₂ (.andI upper (le_trans h.andE₂.andE₂.andE₂.andE₁ (le_add_right _ _)))))
    (.andI h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂)

theorem grid_cell_error (i p z R B a C E T N : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (forward (sampleBody endpointF)) i (sampleData p N a C E (fixedData z B)))
      (inst2 (multiplyBody (sampleBody operatorF)) i (pairT (weight C E N) (sampleData p N a C E (fixedData z B))))
      (GaussianEulerIntegrationByPartsStep.numerator p R E T (E*N) C) (GaussianEulerIntegrationByPartsProductStep.denominator p (E*N)) := by
  have next : Γ ⊢[PRAAx] inst2 (sampleBody endpointF) (succ i) (sampleData p N a C E (fixedData z B)) ≐
      primitive p z B (a*N+C*i+C) (E*N) :=
    (endpoint_grid_at (succ i) p z B a C E N).eqTrans (primitive_numerator_congr p z B _ _ (E*N) (by ipra_ring))
  have first := qsub_congr next (endpoint_grid_at i p z B a C E N)
  have op := (sample_body_at (Γ := Γ) operatorF i p N a C E (fixedData z B)).eqTrans (operator_at p z B (a*N+C*i) (E*N))
  have second := (multiply_body_at (sampleBody operatorF) (weight C E N) i (sampleData p N a C E (fixedData z B))).eqTrans
    (qmul_congr (.eqRefl _) op)
  rw [forward_at]
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerIntegrationByPartsStep.original_cell_error p z R B E T (a*N+C*i) (E*N) C (cell_source i z R B a C E T N h hi))

theorem original_finite_error (p z R B a C E T N : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (qsub (endpoint N p z B a C E N) (endpoint zero p z B a C E N))
      (quadrature operatorF p N a C E (fixedData z B)) (numerator p R E T C N) (denominator p E N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have rows : Γ ⊢[PRAAx] termsDistance (forward (sampleBody endpointF)) (multiplyBody (sampleBody operatorF)) N
      (sampleData p N a C E (fixedData z B)) (pairT (weight C E N) (sampleData p N a C E (fixedData z B)))
      (GaussianEulerIntegrationByPartsStep.numerator p R E T (E*N) C) (GaussianEulerIntegrationByPartsProductStep.denominator p (E*N)) := by
    refine .allI (.impI ?_)
    simpa [termsDistance,GaussianEulerIntegrationByPartsStep.numerator,GaussianEulerIntegrationByPartsStep.curvature,
      GaussianEulerIntegrationByPartsProductStep.curvature,GaussianEulerIntegrationByPartsProductStep.observationCost,
      GaussianEulerIntegrationByPartsProductStep.powerCurvature,GaussianEulerIntegrationByPartsProductStep.linearBound,
      GaussianEulerIntegrationByPartsStep.productSlopeBound,GaussianEulerIntegrationByPartsProductStep.denominator,
      GaussianEulerPowerShiftRate.radius,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius,Syn.shift] using
      grid_cell_error (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) hs.wk Prf.hyp0
  have hE := h.andE₁.andE₁.andE₂.andE₁
  have hN := h.andE₂.andE₁
  have he := positive_product E N hE hN
  have old := GaussianEulerIntegrationByPartsProductStep.denominator_positive p (E*N) he
  have raw := sum_distance (forward (sampleBody endpointF)) (multiplyBody (sampleBody operatorF)) N
    (sampleData p N a C E (fixedData z B)) (pairT (weight C E N) (sampleData p N a C E (fixedData z B)))
    (GaussianEulerIntegrationByPartsStep.numerator p R E T (E*N) C) (GaussianEulerIntegrationByPartsProductStep.denominator p (E*N)) old rows
  have endpoints := grid_telescope (Γ := Γ) p z B a C E N
  have quad := GaussianRationalFiniteSum.sum_multiply (Γ := Γ) (sampleBody operatorF) (weight C E N) N (sampleData p N a C E (fixedData z B))
  have joined := distance_congr endpoints quad (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ old (positive_product _ _ (positive_product _ _ (positive_product E E hE hE) hN) (unit_positive p))
    (le_of_eq_add (d := zero) (by dsimp only [GaussianEulerIntegrationByPartsStep.numerator,GaussianEulerIntegrationByPartsProductStep.denominator,numerator,denominator]; ipra_ring)) joined

theorem original_finite_Euler_integration_by_parts_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (qsub (endpoint (var 8) (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 8))
        (endpoint zero (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 8)))
        (quadrature operatorF (var 0) (var 8) (var 4) (var 5) (var 6) (fixedData (var 1) (var 3)))
        (numerator (var 0) (var 2) (var 6) (var 7) (var 5) (var 8)) (denominator (var 0) (var 6) (var 8))) :=
  closeUniv 9 (.impI (original_finite_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGrid
