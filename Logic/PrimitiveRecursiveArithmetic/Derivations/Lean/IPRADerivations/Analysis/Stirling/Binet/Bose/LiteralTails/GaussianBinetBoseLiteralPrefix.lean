import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseSeriesRows
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Literal finite sum of the original damped exponentials

A sum of the explicit row budgets bounds each original comparison
with the geometric powers at the common observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralPrefix

open_ipra
open GaussianBinetBoseExponential (expF expData)
open GaussianBinetBoseSeries (ratio prefixValue)
open GaussianBinetBoseSeriesRows (rowCost rowClock row_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalReciprocal (power)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def parameters (p A B : PTm n) : PTm n := pairT p (pairT A B)

ipra_subst parameters

ipra_subst rowCost [two]

ipra_subst rowClock [GaussianBinetBoseSeries.denominatorClock, GaussianBinetBoseDenominator.sampleClock, GaussianNameReciprocal.anchor, GaussianNameReciprocal.modulus, two]

@[simp] theorem subst_ratio {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (ratio p A B) = ratio (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  change Syn.subst σ (GaussianRationalReciprocal.reciprocal (ap2 expF (rowClock p B) (expData false A B))) = _
  simp only [GaussianRationalReciprocal.subst_reciprocal, subst_ap2, subst_rowClock, GaussianBinetBoseExponential.subst_expData]
  rfl

def term (i p A B : PTm n) : PTm n := ap2 expF (rowClock p B) (expData true (succ i*A) B)

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (i p A B : PTm n) :
    Syn.subst σ (term i p A B) = term (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [term]

def body : PTm 2 := term (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def costBody : PTm 2 := rowCost (fstT (var 1)) (succ (var 0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

def value (p N A B : PTm n) : PTm n := GaussianRationalFiniteSum.sum body N (parameters p A B)
def budget (N A B : PTm n) : PTm n := ap2 (LeanProofs.IPRA.sumF costBody) N (parameters N A B)

ipra_subst value

ipra_subst budget

theorem value_canonical (p N A B : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (value p N A B) :=
  GaussianRationalFiniteSum.sum_canonical body N (parameters p A B)

private theorem payload_eq (p A B : PTm n) :
    Γ ⊢[PRAAx] ((fstT (parameters p A B) ≐ p) ⋏
      ((fstT (sndT (parameters p A B)) ≐ A) ⋏ (sndT (sndT (parameters p A B)) ≐ B))) := by
  exact .andI (fst_pair p (pairT A B))
    (.andI ((congrFst (snd_pair p (pairT A B))).eqTrans (fst_pair A B))
      ((congrSnd (snd_pair p (pairT A B))).eqTrans (snd_pair A B)))

theorem row_at (i p A B : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (parameters p A B) ≐ term i p A B := by
  let x := parameters p A B
  have e := payload_eq (Γ := Γ) p A B
  simpa only [body,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,x] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (term (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![i,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![i,p,A,B])
      (fun j => by fin_cases j; exact .eqRefl i; exact e.andE₁; exact e.andE₂.andE₁; exact e.andE₂.andE₂)

theorem cost_at (j N A B : PTm n) :
    Γ ⊢[PRAAx] inst2 costBody j (parameters N A B) ≐ rowCost N (succ j) A B := by
  let x := parameters N A B
  have e := payload_eq (Γ := Γ) N A B
  simpa only [costBody,inst2,subst_rowCost,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,x] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowCost (var 0) (succ (var 1)) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,j,fstT (sndT x),sndT (sndT x)]) (σ' := ![N,j,A,B])
      (fun i => by fin_cases i; exact e.andE₁; exact .eqRefl j; exact e.andE₂.andE₁; exact e.andE₂.andE₂)

private theorem common_row (j p N A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] distanceBounded
      (inst2 body j (parameters p A B)) (inst2 GaussianRationalInverseGeometric.body j (ratio p A B))
      (budget N A B) (unit (rowClock p B)) := by
  have hh : Γ ⊢[PRAAx] le (rowCost N (succ j) A B) (budget N A B) :=
    le_congr (cost_at j N A B) (.eqRefl _) (LeanProofs.IPRA.term_le_sum costBody (x := parameters N A B) hj)
  have r := row_error p N (succ j) A B hB hj hN
  have u := unit_positive (Γ := Γ) (rowClock p B)
  have converted := distance_radius_mono _ _ _ _ _ _ u u (mul_le_mul_right (unit (rowClock p B)) hh) r
  have power_at : inst2 GaussianRationalInverseGeometric.body j (ratio p A B) = power (ratio p A B) (succ j) := by
    simp only [GaussianRationalInverseGeometric.body,inst2,GaussianRationalReciprocal.subst_power,
      Syn.subst_var,ConciseIPRA.PTm.subst_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [power_at]
  exact distance_congr (row_at j p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) converted

theorem finite_error (p N A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (value p N A B) (prefixValue p A B N) (N*budget N A B) (unit (rowClock p B)) := by
  have rows : Γ ⊢[PRAAx] termsDistance body GaussianRationalInverseGeometric.body N
      (parameters p A B) (ratio p A B) (budget N A B) (unit (rowClock p B)) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have hn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
    have hb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift
    simpa only [termsDistance, Δ,s,Syn.shift,subst_parameters,subst_ratio,subst_budget,subst_rowClock,
      GaussianCoefficientNameBounds.subst_unit] using
      common_row (var 0) (s p) (s N) (s A) (s B) hn.wk hb.wk Prf.hyp0
  exact sum_distance _ _ _ _ _ _ _ (unit_positive (rowClock p B)) rows

theorem actual_Binet_literal_damped_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 3)) ⟶
      distanceBounded (value (var 0) (var 1) (var 2) (var 3))
        (prefixValue (var 0) (var 2) (var 3) (var 1))
        (var 1*budget (var 1) (var 2) (var 3)) (unit (rowClock (var 0) (var 3)))) :=
  closeUniv 4 (.impI (finite_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralPrefix
