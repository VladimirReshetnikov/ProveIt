import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayMesh

/-!
# The actual compact decay quadrature and its endpoints

The compact left sum of exp(-t) on [a/E,(a+C)/E] differs from the
two actual endpoint observations by at most
3C²/(E²N)+20N·2⁻ᵖ. Each cell uses the original evaluator, common
denominator E*N, and weight C/(E*N).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadrature

open_ipra
open GaussianEulerDecayMesh (observation observation_numerator_congr observation_rescale adjacent_step
  consecutiveDifference consecutive_difference_at consecutive_difference_sum stepError errorDen)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalRiemannRefinement (sum_distance termsDistance weight leftSum)
open GaussianCompactRiemannName (grid sampleBody sampleData quadrature sample_body_at)
open GaussianCoefficientNameBounds (unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluator (p t : PTm n) : PTm n := observation (fstT t) (sndT t) p
def evaluatorF : PR 3 := PTm.toPR (evaluator (var 0) (var 1) : PTm 3)

ipra_subst evaluator

theorem evaluator_at (p a b x : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) x ≐ observation a b p := by
  have read : Γ ⊢[PRAAx] ap3 evaluatorF p (pairT a b) x ≐ evaluator p (pairT a b) := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluator (var 0) (var 1) : PTm 3) ![p,pairT a b,x]
  refine read.eqTrans ?_
  ipra_congr (observation (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl p] using [evaluator]

theorem cell_at (i p N a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (sampleData p N a C E x) ≐ observation (a*N+C*i) (E*N) p :=
  (sample_body_at evaluatorF i p N a C E x).eqTrans (evaluator_at p _ _ x)

/-- The local error estimate at the unwrapped rational nodes of a decay cell. -/
abbrev adjacentError (i p N a C E : PTm n) : Fm PTm n :=
  distanceBounded (qmul (observation (a*N+C*i) (E*N) p) (weight C E N))
    (qsub (observation (a*N+C*i) (E*N) p) (observation (a*N+C*i+C) (E*N) p))
    (stepError (E*N) C p) (errorDen (E*N) p)

/-- Read a local error bound back into the genuine weighted grid cell. -/
theorem cell_distance_of_adjacent (i p N a C E x : PTm n)
    (adjacent : Γ ⊢[PRAAx] adjacentError i p N a C E) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight C E N) (sampleData p N a C E x)))
      (inst2 (consecutiveDifference (sampleBody evaluatorF)) i (sampleData p N a C E x))
      (stepError (E*N) C p) (errorDen (E*N) p) := by
  let f := sampleBody evaluatorF
  let d := sampleData p N a C E x
  let X := observation (a*N+C*i) (E*N) p
  let Y := observation (a*N+C*i+C) (E*N) p
  let w := weight C E N
  have first : Γ ⊢[PRAAx] inst2 (multiplyBody f) i (pairT w d) ≐ qmul X w :=
    (multiply_body_at f w i d).eqTrans ((qmul_congr (.eqRefl _) (cell_at i p N a C E x)).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative w X))
  have next : Γ ⊢[PRAAx] inst2 f (succ i) d ≐ Y :=
    (cell_at (succ i) p N a C E x).eqTrans (observation_numerator_congr _ _ _ _ (by ipra_ring))
  have second : Γ ⊢[PRAAx] inst2 (consecutiveDifference f) i d ≐ qsub X Y := by
    rw [consecutive_difference_at]
    exact qsub_congr (cell_at i p N a C E x) next
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) adjacent

theorem cell_distance (i p N a C E x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight C E N) (sampleData p N a C E x)))
      (inst2 (consecutiveDifference (sampleBody evaluatorF)) i (sampleData p N a C E x))
      (stepError (E*N) C p) (errorDen (E*N) p) :=
  cell_distance_of_adjacent i p N a C E x
    (adjacent_step (a*N+C*i) (E*N) C p
      (le_trans (positive_product a N ha hN) (le_add_right _ _)) (positive_product E N hE hN) hC hstep)

theorem endpoint_left_at (p N a C E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) zero (sampleData p N a C E x) ≐ observation a E p :=
  (cell_at zero p N a C E x).eqTrans ((observation_numerator_congr _ _ _ _ (by ipra_ring)).eqTrans
    (observation_rescale a E N p hE hN))

theorem endpoint_right_at (p N a C E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) N (sampleData p N a C E x) ≐ observation (a+C) E p :=
  (cell_at N p N a C E x).eqTrans ((observation_numerator_congr _ _ _ _ (by ipra_ring)).eqTrans
    (observation_rescale (a+C) E N p hE hN))

/-- Sum the local error estimates and telescope the original consecutive differences. -/
theorem quadrature_of_adjacent (p N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (adjacent : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
      adjacentError (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N a C E x)
      (qsub (observation a E p) (observation (a+C) E p))
      (N*stepError (E*N) C p) (errorDen (E*N) p) := by
  let f := sampleBody evaluatorF
  let w := weight C E N
  let d := sampleData p N a C E x
  let A := stepError (E*N) C p
  let D := errorDen (E*N) p
  have hb := positive_product E N hE hN
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hb hb) (unit_positive p)
  have entries : Γ ⊢[PRAAx] termsDistance (multiplyBody f) (consecutiveDifference f) N (pairT w d) d A D := by
    refine .allI (.impI ?_)
    simpa [termsDistance,A,D,w,d,f,Syn.shift,stepError,errorDen,GaussianNameRingLaws.three] using
      cell_distance_of_adjacent (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift x) adjacent
  have endpoints := (consecutive_difference_sum f d N).eqTrans
    (qsub_congr (endpoint_left_at p N a C E x hE hN) (endpoint_right_at p N a C E x hE hN))
  exact distance_congr (sum_multiply f w N d) endpoints (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ hD entries)

theorem actual_decay_quadrature (p N a C E x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N a C E x)
      (qsub (observation a E p) (observation (a+C) E p))
      (N*stepError (E*N) C p) (errorDen (E*N) p) := by
  apply quadrature_of_adjacent p N a C E x hN hE
  have left := positive_product _ _ (Order.shift_one_le ha) (Order.shift_one_le hN)
  have den := positive_product _ _ (Order.shift_one_le hE) (Order.shift_one_le hN)
  have step : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift C) (Syn.shift E*Syn.shift N) :=
    by simpa [Fm.shift,Syn.shift] using hstep.shift
  exact adjacent_step _ _ _ _ (le_trans left.wk (le_add_right _ _)) den.wk (Order.shift_one_le hC).wk step.wk

theorem original_compact_decay_quadrature_endpoint_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 2) ⋏ le one (var 1)) ⟶ (le one (var 4) ⋏ le one (var 3)) ⟶
        le (var 3) (var 4*var 1) ⟶
        distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (qsub (observation (var 2) (var 4) (var 0)) (observation (var 2+var 3) (var 4) (var 0)))
          (var 1*stepError (var 4*var 1) (var 3) (var 0)) (errorDen (var 4*var 1) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (actual_decay_quadrature _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadrature
