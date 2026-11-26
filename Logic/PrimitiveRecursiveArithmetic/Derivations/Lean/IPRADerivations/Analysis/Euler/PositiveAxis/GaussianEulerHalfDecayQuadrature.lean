import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayQuadraturePrecision

/-!
# Exact half-decay change of variables on the original compact grid

The actual evaluator of exp(-t/2) reuses the original decay sampler
at the doubled time denominator. Its compact left sum is twice the
original decay quadrature on the half-sized interval. This transfers
the independent endpoint error to the upper-tail majorant kernel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerDecayQuadrature (evaluatorF evaluator_at)
open GaussianEulerDecayQuadraturePrecision (endpointDifference independent_quadrature_endpoint numerator denominator)
open GaussianCompactRiemannName (sampleBody sampleData quadrature sample_body_at)
open GaussianRationalRiemannRefinement (weight weight_repetition leftSum)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluator (p t x : PTm n) : PTm n := ap3 evaluatorF p (pairT (fstT t) (two*sndT t)) x
def halfF : PR 3 := PTm.toPR (evaluator (var 0) (var 1) (var 2))

@[simp] theorem subst_evaluator {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluator p t x) = evaluator (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) :=
  by simp [evaluator]

theorem half_at (p a b x : PTm n) :
    Γ ⊢[PRAAx] ap3 halfF p (pairT a b) x ≐ ap3 evaluatorF p (pairT a (two*b)) x := by
  have e : Γ ⊢[PRAAx] ap3 halfF p (pairT a b) x ≐ evaluator p (pairT a b) x := by
    simpa [halfF,ap3] using toPR_eq (Γ := Γ) (evaluator (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,x]
  exact e.eqTrans (congrAp3 evaluatorF (.eqRefl _)
    (congrPairT (fst_pair a b) (congrMul (.eqRefl two) (snd_pair a b))) (.eqRefl x))

theorem cell_at (i p N a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody halfF) i (sampleData p N a C E x) ≐
      inst2 (sampleBody evaluatorF) i (sampleData p N a C (two*E) x) := by
  have e : Γ ⊢[PRAAx] two*(E*N) ≐ (two*E)*N := by ipra_ring
  exact (sample_body_at halfF i p N a C E x).eqTrans
    ((half_at p (a*N+C*i) (E*N) x).eqTrans
      ((congrAp3 evaluatorF (.eqRefl p) (congrPairT (.eqRefl (a*N+C*i)) e) (.eqRefl x)).eqTrans
        (sample_body_at evaluatorF i p N a C (two*E) x).eqSymm))

theorem half_weight (C E N : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qmul (naturalPoint two) (weight C (two*E) N) ≐ weight C E N := by
  have e : Γ ⊢[PRAAx] weight C (two*E) N ≐ weight C E (two*N) :=
    GaussianCompactRiemannName.fraction_congr C C _ _ (.eqRefl _) (by ipra_ring)
  exact (qmul_congr (.eqRefl _) e).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (weight_repetition C E two N hE (le_succ_self one) hN))

theorem actual_half_decay_quadrature (p N a C E x : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] quadrature halfF p N a C E x ≐
      qmul (naturalPoint two) (quadrature evaluatorF p N a C (two*E) x) := by
  let f := sampleBody halfF
  let g := sampleBody evaluatorF
  let X := sampleData p N a C E x
  let Y := sampleData p N a C (two*E) x
  have same : Γ ⊢[PRAAx] termsEqual f g N X Y := by
    refine .allI (.impI ?_)
    simpa [termsEqual,f,g,X,Y,Syn.shift] using
      (cell_at (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a)
        (Syn.shift C) (Syn.shift E) (Syn.shift x))
  have eq := GaussianRationalFiniteSum.sum_congr_bounded f g N X Y same
  exact (qmul_congr (half_weight C E N hE hN).eqSymm eq).eqTrans
    (GaussianReciprocalHorner.qmul_associative (naturalPoint two) (weight C (two*E) N) (sum g N Y))

theorem half_decay_independent_endpoint (p q N a C E x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature halfF p N a C E x)
      (qmul (naturalPoint two) (endpointDifference a C (two*E) q))
      (two*numerator p q N C (two*E)) (denominator p q N (two*E)) := by
  have hpos := positive_product two E (le_succ_self one) hE
  have hb := positive_product _ _ hpos hpos
  have hD : Γ ⊢[PRAAx] le one (denominator p q N (two*E)) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ hb hN) (unit_positive p)) (unit_positive q)
  have bound : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (naturalPoint two) two one :=
    GaussianRationalReciprocal.bound_congr
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point two one (le_refl one)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded two one (le_refl one))
  exact distance_congr (actual_half_decay_quadrature p N a C E x hE hN).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (naturalPoint two) _ _ two _ _ hD bound
      (independent_quadrature_endpoint p q N a C (two*E) x ha hN hpos hC hstep))

theorem original_half_decay_grid_change_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ le one (var 1) ⟶
      quadrature halfF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
        qmul (naturalPoint two) (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (two*var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (actual_half_decay_quadrature _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_half_decay_endpoint_estimate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 3) ⋏ le one (var 2)) ⟶ (le one (var 5) ⋏ le one (var 4)) ⟶ le (var 4) ((two*var 5)*var 2) ⟶
      distanceBounded (quadrature halfF (var 0) (var 2) (var 3) (var 4) (var 5) (var 6))
        (qmul (naturalPoint two) (endpointDifference (var 3) (var 4) (two*var 5) (var 1)))
        (two*numerator (var 0) (var 1) (var 2) (var 4) (two*var 5))
        (denominator (var 0) (var 1) (var 2) (two*var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (half_decay_independent_endpoint _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayQuadrature
