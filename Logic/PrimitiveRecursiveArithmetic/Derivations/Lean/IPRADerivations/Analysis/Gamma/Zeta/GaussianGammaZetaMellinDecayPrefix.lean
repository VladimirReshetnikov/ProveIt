import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinDecayRows
import IPRADerivations.Core.SumLemmas

/-!
# Actual Euler decay prefix of the Mellin integrand

All decay terms use the original Euler exponential at their actual
integer multiples of the time. One power observation, at the original
Mellin product clock, multiplies every term in the prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 740000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDecayPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegrandName (decayF decayData powerF powerData source)
open GaussianGammaZetaMellinDecayRows (clock rowCost prefix_row_error)
open GaussianGammaZetaMellinGeometric (ratio prefixValue)
open GaussianGammaZetaMellinIntegrand (factorClock)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def parameters (p a b : PTm n) : PTm n := pairT p (pairT a b)
def term (j p a b : PTm n) : PTm n := ap2 decayF (clock p b) (decayData (succ j*a) b)
def body : PTm 2 := term (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def value (p N a b : PTm n) : PTm n := sum body N (parameters p a b)

private def costBody : PTm 2 := rowCost (fstT (var 1)) (succ (var 0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

def rowBudget (N a b : PTm n) : PTm n := ap2 (LeanProofs.IPRA.sumF costBody) N (parameters N a b)
def roundingCost (N a b : PTm n) : PTm n := N*rowBudget N a b

def powerSample (p z D a b : PTm n) : PTm n := ap2 powerF (factorClock p z D a b) (powerData z D a b)
def weightedValue (p z D a b N : PTm n) : PTm n :=
  qmul (powerSample p z D a b) (value (factorClock p z D a b) N a b)

def errorNumerator (h H N P : PTm n) : PTm n := P*((H*H)*unit h+(H+N))
def errorDenominator (h H N : PTm n) : PTm n := (H+N)*unit h

@[simp] theorem subst_parameters {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (parameters p a b) = parameters (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [parameters]
@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (j p a b : PTm n) :
    Syn.subst σ (term j p a b) = term (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [term]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p N a b : PTm n) :
    Syn.subst σ (value p N a b) = value (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [value]
@[simp] theorem subst_rowBudget {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (rowBudget N a b) = rowBudget (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [rowBudget]
@[simp] theorem subst_roundingCost {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (roundingCost N a b) = roundingCost (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [roundingCost]
@[simp] theorem subst_powerSample {m : ℕ} (σ : Fin n → PTm m) (p z D a b : PTm n) :
    Syn.subst σ (powerSample p z D a b) =
      powerSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [powerSample,factorClock]
@[simp] theorem subst_weightedValue {m : ℕ} (σ : Fin n → PTm m) (p z D a b N : PTm n) :
    Syn.subst σ (weightedValue p z D a b N) =
      weightedValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [weightedValue,factorClock]
@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (h H N P : PTm n) :
    Syn.subst σ (errorNumerator h H N P) = errorNumerator (Syn.subst σ h) (Syn.subst σ H) (Syn.subst σ N) (Syn.subst σ P) := by
  simp [errorNumerator]
@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (h H N : PTm n) :
    Syn.subst σ (errorDenominator h H N) = errorDenominator (Syn.subst σ h) (Syn.subst σ H) (Syn.subst σ N) := by
  simp [errorDenominator]

private theorem decode (q : Fin 4 → PTm n) (j p a b : PTm n) (x : PTm 4)
    (h : q = ![j,fstT (parameters p a b),fstT (sndT (parameters p a b)),sndT (sndT (parameters p a b))]) :
    Γ ⊢[PRAAx] Syn.subst q x ≐ Syn.subst ![j,p,a,b] x := by
  subst q
  have pair := snd_pair (Γ := Γ) p (pairT a b)
  exact Prf.eqCongr x (fun i => by
    fin_cases i
    · exact .eqRefl j
    · exact fst_pair p (pairT a b)
    · exact (congrFst pair).eqTrans (fst_pair a b)
    · exact (congrSnd pair).eqTrans (snd_pair a b))

theorem term_at (j p a b : PTm n) : Γ ⊢[PRAAx] inst2 body j (parameters p a b) ≐ term j p a b := by
  have read := decode (Γ := Γ) _ j p a b (term (var 0) (var 1) (var 2) (var 3)) rfl
  simpa only [body,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using read

theorem row_budget (j N a b : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] le (rowCost N (succ j) a b) (rowBudget N a b) := by
  have read := decode (Γ := Γ) _ j N a b (rowCost (var 1) (succ (var 0)) (var 2) (var 3)) rfl
  have eq : Γ ⊢[PRAAx] inst2 costBody j (parameters N a b) ≐ rowCost N (succ j) a b := by
    simpa only [costBody,inst2,GaussianGammaZetaMellinDecayRows.subst_rowCost,ConciseIPRA.PTm.subst_succ,
      subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using read
  exact le_congr eq (.eqRefl _) (LeanProofs.IPRA.term_le_sum costBody hj)

theorem prefix_error (p N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (value p N a b) (prefixValue p a b N)
      (roundingCost N a b) (unit (clock p b)) := by
  let G := GaussianRationalInverseGeometric.body
  let X := parameters p a b
  let Y := ratio p a b
  let P := rowBudget N a b
  let U := unit (clock p b)
  have hu := unit_positive (Γ := Γ) (clock p b)
  have rows : Γ ⊢[PRAAx] termsDistance body G N X Y P U := by
    refine .allI (.impI ?_)
    let s (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have bs : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hb.shift.wk
    have j : Δ ⊢[PRAAx] lt (var 0) (s N) := Prf.hyp0
    have z := prefix_row_error (s p) (s N) (var 0) (s a) (s b) bs j (le_trans (zero_lt_succ _) j)
    have uz := unit_positive (Γ := Δ) (clock (s p) (s b))
    have lo := mul_le_mul_right (unit (clock (s p) (s b))) (row_budget (var 0) (s N) (s a) (s b) j)
    have close := distance_radius_mono _ _ _ _ _ _ uz uz lo z
    simpa only [Δ,s,G,X,Y,P,U,Syn.shift,subst_parameters,subst_rowBudget,
      GaussianGammaZetaMellinDecayRows.subst_clock,GaussianGammaZetaMellinGeometric.subst_ratio,
      GaussianCoefficientNameBounds.subst_unit] using
      distance_congr (term_at (var 0) (s p) (s a) (s b)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) close
  exact sum_distance _ _ N X Y P U hu rows

theorem weighted_sum_at (p z D a b N : PTm n) :
    let k := factorClock p z D a b
    Γ ⊢[PRAAx] weightedValue p z D a b N ≐
      sum (multiplyBody body) N (pairT (powerSample p z D a b) (parameters k a b)) :=
  (sum_multiply body _ _ _).eqSymm

theorem weighted_term_at (j p z D a b : PTm n) :
    let k := factorClock p z D a b
    Γ ⊢[PRAAx] inst2 (multiplyBody body) j (pairT (powerSample p z D a b) (parameters k a b)) ≐
      qmul (powerSample p z D a b) (term j k a b) :=
  (multiply_body_at body _ j _).eqTrans (qmul_congr (.eqRefl _) (term_at j _ a b))

theorem weighted_error (p h z D a b N H P : PTm n)
    (hs : Γ ⊢[PRAAx] source z D a b) (hH : Γ ⊢[PRAAx] le one H)
    (ht : Γ ⊢[PRAAx] le b (H*a)) (hP : Γ ⊢[PRAAx] bounded (powerSample p z D a b) P one)
    (hk : Γ ⊢[PRAAx] le (roundingCost N a b*unit h) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (weightedValue p z D a b N)
      (ap2 GaussianGammaZetaMellinIntegrand.nameF p (GaussianGammaZetaMellinIntegrand.data z D a b))
      (errorNumerator h H N P) (errorDenominator h H N) := by
  let k := factorClock p z D a b
  let r := clock k b
  let U := unit h
  let Z := H+N
  let F := errorDenominator h H N
  have hp : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hr : Γ ⊢[PRAAx] le k r :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have room := le_trans hk (GaussianExponentialReference.unit_monotone (le_trans hp hr))
  have hU := unit_positive (Γ := Γ) h
  have hZ := le_trans hH (le_add_right H N)
  have hF := positive_product _ _ hZ hU
  have short := distance_radius_mono _ _ _ _ one U (unit_positive r) hU
    (le_congr (.eqRefl _) (one_mul (unit r)).eqSymm room) (prefix_error k N a b hs.andE₂.andE₂)
  have factor := GaussianApproximateInverseDistance.multiply_distance (powerSample p z D a b) _ _ P one U hU hP short
  have left := distance_radius_mono _ _ _ _ (P*Z) F hU hF
    (le_of_eq_add (d := zero) (by dsimp only [Z,F,errorDenominator,U]; ipra_ring)) factor
  have geometric := GaussianGammaZetaMellinGeometric.integrand_error_on_strip p z D a b N H P hs hH ht hP
  have right := distance_radius_mono _ _ _ _ ((P*(H*H))*U) F hZ hF
    (le_of_eq_add (d := zero) (by dsimp only [Z,F,errorDenominator,U]; ipra_ring)) geometric
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [Z,U,errorNumerator]; ipra_ring) (.eqRefl F)
    (distance_triangle_same _ _ _ _ _ _ hF left right)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDecayPrefix
