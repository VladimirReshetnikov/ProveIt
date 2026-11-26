import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmWeightedNorm
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference

/-!
# Geometric Taylor remainder for the original finite Mercator polynomial

The coefficient of degree (k+1) has norm (1/(k+1)). In a suffix
starting at degree (m+1), the finite geometric numerator telescopes
with ratio (R/N) while (1/(m+1)) bounds all coefficient norms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmTaylorRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianFiniteLogarithmPolynomial (coefficient signNumerator value sourceTerm)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded bounded_of_cleared)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal (power bounded_power bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (R m : PTm n) : PTm n := pw R (succ m)
def denominator (R N m : PTm n) : PTm n := succ m*monus N R*pw N m

def finiteNumerator (R N m r : PTm n) : PTm n := numerator R m*monus (pw N r) (pw R r)
def finiteDenominator (R N m r : PTm n) : PTm n := denominator R N m*pw N r

def tail (m r w : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum (offB sourceTerm) r (pairT m w)

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (numerator R m) = numerator (Syn.subst σ R) (Syn.subst σ m) :=
  by simp [numerator]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (R N m : PTm n) :
    Syn.subst σ (denominator R N m) = denominator (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ m) :=
  by simp [denominator]

@[simp] theorem subst_finiteNumerator {l : ℕ} (σ : Fin n → PTm l) (R N m r : PTm n) :
    Syn.subst σ (finiteNumerator R N m r) = finiteNumerator (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ r) :=
  by simp [finiteNumerator]

@[simp] theorem subst_finiteDenominator {l : ℕ} (σ : Fin n → PTm l) (R N m r : PTm n) :
    Syn.subst σ (finiteDenominator R N m r) = finiteDenominator (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ r) :=
  by simp [finiteDenominator]

@[simp] theorem subst_tail {l : ℕ} (σ : Fin n → PTm l) (m r w : PTm n) :
    Syn.subst σ (tail m r w) = tail (Syn.subst σ m) (Syn.subst σ r) (Syn.subst σ w) :=
  by simp [tail]

theorem denominator_positive (R N m : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N) :
    Γ ⊢[PRAAx] le one (denominator R N m) := by
  have e := eq_add_of_le (le_of_lt hRN)
  have hg : Γ ⊢[PRAAx] le one (monus N R) :=
    le_of_add_le_add_right (le_congr (by ipra_ring) (e.eqTrans (add_comm _ _)) hRN)
  exact positive_product _ _ (positive_product _ _ (zero_lt_succ m) hg) (GaussianFactorBudget.power_positive _ _ hN)

theorem finite_denominator_positive (R N m r : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N) :
    Γ ⊢[PRAAx] le one (finiteDenominator R N m r) :=
  positive_product _ _ (denominator_positive R N m hN hRN) (GaussianFactorBudget.power_positive _ _ hN)

theorem coefficient_bound (k : PTm n) : Γ ⊢[PRAAx] bounded (coefficient k) one (succ k) := by
  have hr := GaussianFiniteLogarithmWeightedNorm.sign_norm1 (Γ := Γ) k
  have norm := le_congr (.eqRefl _) (congrMul hr hr)
    (GaussianL1.normSq_le_norm1_square (signNumerator k))
  exact bounded_of_cleared _ _ _ _ _ (zero_lt_succ k) (zero_lt_succ k)
    (GaussianFiniteLogarithmPolynomial.coefficient_represents k)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (succ k*succ k) norm))

private theorem row_bound (m r w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hw : Γ ⊢[PRAAx] bounded w R N) :
    Γ ⊢[PRAAx] bounded (inst2 (offB sourceTerm) r (pairT m w)) (pw R (succ (m+r))) (succ m*pw N (succ (m+r))) := by
  let k := m+r
  let e := succ k
  have hp := GaussianFactorBudget.power_positive (Γ := Γ) N e hN
  have hc := coefficient_bound (Γ := Γ) k
  have b := bound_congr (.eqRefl _) (one_mul _) (.eqRefl _)
    (bounded_product _ _ one (succ k) (pw R e) (pw N e) (zero_lt_succ k) hp hc (bounded_power w R N e hN hw))
  have hmk : Γ ⊢[PRAAx] le (succ m) (succ k) :=
    le_congr (succ_eq_add_one m).eqSymm (succ_eq_add_one k).eqSymm
      (add_le_add_right one (le_add_right m r))
  have fit : Γ ⊢[PRAAx] le (pw R e*(succ m*pw N e)) (pw R e*(succ k*pw N e)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (pw R e*pw N e) hmk)
  have raw := bounded_radius_mono _ _ _ (pw R e) (succ m*pw N e) (positive_product _ _ (zero_lt_succ k) hp)
    (positive_product _ _ (zero_lt_succ m) hp) fit b
  have read : Γ ⊢[PRAAx] inst2 (offB sourceTerm) r (pairT m w) ≐ qmul (coefficient k) (power w e) := by
    simpa only [GaussianFiniteLogarithmPolynomial.source_term_at,k,e] using
      GaussianRationalFiniteProduct.offset_at (Γ := Γ) sourceTerm m r w
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) raw

private theorem geometric_step (R N r : PTm n) (hRN : Γ ⊢[PRAAx] le R N) :
    Γ ⊢[PRAAx] monus (pw N (succ r)) (pw R (succ r)) ≐
      N*monus (pw N r) (pw R r)+monus N R*pw R r := by
  have a := natEq (eq_add_of_le hRN)
  have b := natEq (eq_add_of_le (pw_le_pw r hRN))
  have c := natEq (eq_add_of_le (pw_le_pw (succ r) hRN))
  have d := natEq (pw_succ (Γ := Γ) N r)
  have e := natEq (pw_succ (Γ := Γ) R r)
  apply deriveNat
  simp only [Q.mk_add,map_add,Q.mk_mul,map_mul] at a b c d e ⊢
  linear_combination -c+d-e+𝔞(N)*b+𝔞(pw R r)*a

private theorem finite_zero (m w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N) :
    Γ ⊢[PRAAx] bounded (tail m zero w) (finiteNumerator R N m zero) (finiteDenominator R N m zero) := by
  let D := finiteDenominator R N m zero
  have hD := finite_denominator_positive R N m zero hN hRN
  have b : Γ ⊢[PRAAx] bounded (qzero : PTm n) zero D :=
    bounded_of_cleared _ ComplexLogarithmRemainder.zeroCode one zero D (le_refl one) hD
      (GaussianRationalHorner.zero_represents one)
      (le_congr ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_zero).eqTrans (mul_zero _)).eqSymm
        (by ipra_ring) (le_refl zero))
  have p : Γ ⊢[PRAAx] monus (pw N zero) (pw R zero) ≐ zero :=
    (congrMonus (pw_zero N) (pw_zero R)).eqTrans (monus_self one)
  have a : Γ ⊢[PRAAx] finiteNumerator R N m zero ≐ zero :=
    (congrMul (.eqRefl _) p).eqTrans (mul_zero _)
  exact bound_congr (GaussianRationalFiniteSum.sum_zero (offB sourceTerm) (pairT m w)).eqSymm a.eqSymm (.eqRefl _) b

private theorem finite_succ (m r w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N)
    (hw : Γ ⊢[PRAAx] bounded w R N)
    (ih : Γ ⊢[PRAAx] bounded (tail m r w) (finiteNumerator R N m r) (finiteDenominator R N m r)) :
    Γ ⊢[PRAAx] bounded (tail m (succ r) w) (finiteNumerator R N m (succ r)) (finiteDenominator R N m (succ r)) := by
  let k := succ (m+r)
  let G := monus N R
  let C := finiteNumerator R N m r
  let D := finiteDenominator R N m r
  let E := finiteDenominator R N m (succ r)
  let X := pw R k
  let Y := succ m*pw N k
  let row := inst2 (offB sourceTerm) r (pairT m w)
  have hD := finite_denominator_positive R N m r hN hRN
  have hE := finite_denominator_positive R N m (succ r) hN hRN
  have hY : Γ ⊢[PRAAx] le one Y :=
    positive_product _ _ (zero_lt_succ m) (GaussianFactorBudget.power_positive N k hN)
  have den0 : Γ ⊢[PRAAx] E ≐ N*D :=
    (congrMul (.eqRefl _) (pw_succ N r)).eqTrans (by dsimp only [D,finiteDenominator]; ipra_ring)
  have e (A : PTm n) : Γ ⊢[PRAAx] pw A k ≐ pw A m*pw A (succ r) := by
    have deg : Γ ⊢[PRAAx] k ≐ m+succ r := (add_succ m r).eqSymm
    exact (congrAp2 powF deg (.eqRefl _)).eqTrans (pw_add A m (succ r))
  have den1 : Γ ⊢[PRAAx] E ≐ G*Y := by
    have p := natEq (e N)
    unfold E finiteDenominator denominator G Y
    apply deriveNat
    ipra_simps
    rw [p]
    ring
  have left := bounded_radius_mono _ _ _ (N*C) E hD hE
    (le_congr (congrMul (.eqRefl C) den0).eqSymm (.eqRefl _) (le_of_eq_add (d := zero) (by ipra_ring))) ih
  have right := bounded_radius_mono _ _ _ (G*X) E hY hE
    (le_congr (congrMul (.eqRefl X) den1).eqSymm (.eqRefl _) (le_of_eq_add (d := zero) (by ipra_ring)))
    (row_bound m r w R N hN hw)
  have x : Γ ⊢[PRAAx] X ≐ numerator R m*pw R r := by
    have deg : Γ ⊢[PRAAx] k ≐ succ m+r := (add_succ m r).eqSymm.eqTrans (by ipra_ring)
    exact (congrAp2 powF deg (.eqRefl _)).eqTrans (pw_add R (succ m) r)
  have norm : Γ ⊢[PRAAx] N*C+G*X ≐ finiteNumerator R N m (succ r) := by
    have a := natEq (geometric_step R N r (le_of_lt hRN))
    have b := natEq x
    unfold C G finiteNumerator
    apply deriveNat
    ipra_simps
    rw [a,b]
    ring
  have read : Γ ⊢[PRAAx] tail m (succ r) w ≐ qadd (tail m r w) row :=
    GaussianRationalFiniteSum.sum_succ _ _ _
  exact bound_congr read.eqSymm norm (.eqRefl _) (bounded_sum_same _ _ _ _ _ hE left right)

theorem finite_tail (m r w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N)
    (hw : Γ ⊢[PRAAx] bounded w R N) :
    Γ ⊢[PRAAx] bounded (tail m r w) (finiteNumerator R N m r) (finiteDenominator R N m r) := by
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have all : Γ ⊢[PRAAx] .all (bounded (tail (sh m) (var 0) (sh w))
      (finiteNumerator (sh R) (sh N) (sh m) (var 0)) (finiteDenominator (sh R) (sh N) (sh m) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [GaussianRationalMetric.subst_bounded,subst_tail,subst_finiteNumerator,subst_finiteDenominator,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using finite_zero m w R N hN hRN
    · have hN' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hN.shift
      have hRN' : Δ ⊢[PRAAx] lt (sh R) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hRN.shift
      have hw' : Δ ⊢[PRAAx] bounded (sh w) (sh R) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hw.shift
      simpa only [GaussianRationalMetric.subst_bounded,subst_tail,subst_finiteNumerator,subst_finiteDenominator,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        finite_succ (sh m) (var 0) (sh w) (sh R) (sh N) hN'.wk hRN'.wk hw'.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded,subst_tail,subst_finiteNumerator,subst_finiteDenominator,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE r

theorem exact_difference (m r w : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalMetric.qsub (value (m+r) w) (value m w) ≐ tail m r w :=
  (qsub_congr (GaussianRationalMatrixFiniteSums.sum_split sourceTerm m r w) (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (GaussianRationalFiniteSum.sum_canonical _ _ _))

theorem finite_remainder (m r w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N)
    (hw : Γ ⊢[PRAAx] bounded w R N) :
    Γ ⊢[PRAAx] distanceBounded (value (m+r) w) (value m w) (finiteNumerator R N m r) (finiteDenominator R N m r) :=
  bound_congr (exact_difference m r w).eqSymm (.eqRefl _) (.eqRefl _) (finite_tail m r w R N hN hRN hw)

theorem remainder (m r w R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hRN : Γ ⊢[PRAAx] lt R N)
    (hw : Γ ⊢[PRAAx] bounded w R N) :
    Γ ⊢[PRAAx] distanceBounded (value (m+r) w) (value m w) (numerator R m) (denominator R N m) := by
  have h := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) (pw N r) (pw R r)
  exact bounded_radius_mono _ _ _ _ _ (finite_denominator_positive R N m r hN hRN) (denominator_positive R N m hN hRN)
    (le_congr (by unfold finiteNumerator; ipra_ring) (by unfold finiteDenominator; ipra_ring)
      (mul_le_mul_right (numerator R m*denominator R N m) h))
    (finite_remainder m r w R N hN hRN hw)

theorem actual_finite_Mercator_geometric_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let m := var 0
     let r := var 1
     let w := var 2
     let R := var 3
     let N := var 4
     (le one N ⋏ (lt R N ⋏ bounded w R N)) ⟶
       distanceBounded (value (m+r) w) (value m w) (finiteNumerator R N m r) (finiteDenominator R N m r)) :=
  closeUniv 5 (.impI (finite_remainder _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmTaylorRemainder
