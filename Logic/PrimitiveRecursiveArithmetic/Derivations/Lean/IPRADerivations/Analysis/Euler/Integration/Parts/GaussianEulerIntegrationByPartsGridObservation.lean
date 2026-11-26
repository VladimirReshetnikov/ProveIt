import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsObservation
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# The unchanged Euler quadrature versus its original power-decay rows

An actual PR3 evaluator returns the same-precision original power and
decay product. Every original affine-grid time satisfies the original
compact source. The proved observation comparison, original finite sum
metric and actual compact weight give an error uniform in the mesh
count, including a zero-width interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGridObservation

open_ipra
open GaussianEulerIntegrationByPartsLinear (originalProduct)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (sampleBody sampleData quadrature grid)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawTerm (p t x : PTm n) : PTm n := originalProduct p (fstT x) (sndT x) (fstT t) (sndT t)
def rawF : PR 3 := PTm.toPR (rawTerm (var 0) (var 1) (var 2))
def rowCost (R E T : PTm n) : PTm n := GaussianEulerIntegrationByPartsObservation.factor R E T+one
ipra_subst rawTerm
ipra_subst rowCost [GaussianEulerIntegrationByPartsObservation.factor, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius]

theorem raw_evaluator_at (p a b z B : PTm n) : Γ ⊢[PRAAx]
    ap3 rawF p (pairT a b) (fixedData z B) ≐ originalProduct p z B a b := by
  have read : Γ ⊢[PRAAx] ap3 rawF p (pairT a b) (fixedData z B) ≐ rawTerm p (pairT a b) (fixedData z B) :=
    by simpa only [rawF,ap3,subst_rawTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (rawTerm (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,fixedData z B]
  have value := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (originalProduct (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,fstT (fixedData z B),sndT (fixedData z B),fstT (pairT a b),sndT (pairT a b)]) (σ' := ![p,z,B,a,b])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _; exact fst_pair _ _; exact snd_pair _ _)
  exact read.eqTrans (by simpa only [rawTerm,GaussianEulerIntegrationByPartsLinear.subst_originalProduct,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using value)

theorem raw_grid_at (i p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody rawF) i (sampleData p N a C E (fixedData z B)) ≐ originalProduct p z B (a*N+C*i) (E*N) :=
  (GaussianCompactRiemannName.sample_body_at rawF i p N a C E _).eqTrans (raw_evaluator_at p _ _ z B)

theorem grid_source (i N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsObservation.source z R B E T (a*N+C*i) (E*N) := by
  have ha := h.andE₂.andE₁
  have hE := h.andE₁.andE₂.andE₁
  have htime : Γ ⊢[PRAAx] le N (a*N+C*i) := le_trans
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N ha)) (le_add_right _ _)
  have low : Γ ⊢[PRAAx] le (E*N) (E*(a*N+C*i)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E htime)
  have index : Γ ⊢[PRAAx] le (C*i) (C*N) := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right C hi)
  have first : Γ ⊢[PRAAx] le (a*N+C*i) ((a+C)*N) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl (a*N)) index)
  have last : Γ ⊢[PRAAx] le ((a+C)*N) (T*(E*N)) := le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right N h.andE₂.andE₂)
  exact .andI h.andE₁ (.andI (.andI (le_trans hN htime) (positive_product E N hE hN)) (.andI low (le_trans first last)))

theorem grid_row_error (i p N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData z B)))
      (inst2 (sampleBody rawF) i (sampleData p N a C E (fixedData z B))) (rowCost R E T) (unit p) :=
  distance_congr (GaussianCompactRiemannName.sample_body_at evaluatorF i p N a C E _).eqSymm
    (raw_grid_at i p N z B a C E).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerIntegrationByPartsObservation.original_diagonal p z R B E T (a*N+C*i) (E*N) (grid_source i N z R B a C E T h hN (le_of_lt hi)))

theorem original_grid_observations (p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p N a C E (fixedData z B)) (quadrature rawF p N a C E (fixedData z B))
      (C*rowCost R E T) (E*unit p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody evaluatorF) (sampleBody rawF) N
      (sampleData p N a C E (fixedData z B)) (sampleData p N a C E (fixedData z B)) (rowCost R E T) (unit p) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
      subst_rowCost,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
      grid_row_error (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs.wk ns.wk Prf.hyp0
  have raw := sum_distance _ _ _ _ _ _ _ (unit_positive p) rows
  have hE := h.andE₁.andE₂.andE₁
  have hEN := positive_product E N hE hN
  have scale := GaussianRationalReciprocal.bounded_product _ _ C (E*N) (N*rowCost R E T) (unit p) hEN (unit_positive p)
    (weight_bound C E N hE hN) raw
  have difference := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) scale
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hEN (unit_positive p)) (positive_product _ _ hE (unit_positive p))
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) difference

theorem actual_original_Euler_grid_vs_power_decay_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 1)) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))
        (quadrature rawF (var 0) (var 1) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))
        (var 6*rowCost (var 3) (var 7) (var 8)) (var 7*unit (var 0))) :=
  closeUniv 10 (.impI (original_grid_observations _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGridObservation
