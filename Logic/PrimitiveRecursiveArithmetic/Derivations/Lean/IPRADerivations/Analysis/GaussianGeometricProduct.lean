import IPRADerivations.Analysis.GaussianFactorBudget
import IPRADerivations.Analysis.RationalNonnegativePowers

/-!
# Actual finite products of geometrically shrinking rational factors

The numerator and denominator are actual recursors, initially one. At
stage j they multiply by K^j+C*(pred K)^j and K^j respectively. Their
normalized quotient is therefore the finite product of 1+C*rho^j, with
rho=(pred K)/K. Genuine QF induction proves positivity and the coarse
prefix bound; no global product bound or iteration law is assumed. All
parameters and stage indices remain internal, including C=0 and K=1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeometricProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalNonnegativePowers (power)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factor (C K j : PTm n) : PTm n := pw K j+C*pw (pred K) j
def numeratorStep : PTm 4 := var 1*factor (var 2) (var 3) (var 0)
def denominatorStep : PTm 4 := var 1*pw (var 3) (var 0)
def numeratorF : PR 3 := recDef (one : PTm 2) numeratorStep
def denominatorF : PR 3 := recDef (one : PTm 2) denominatorStep
def numerator (C K j : PTm n) : PTm n := ap3 numeratorF j C K
def denominator (C K j : PTm n) : PTm n := ap3 denominatorF j C K
def value (C K j : PTm n) : PTm n := fraction (numerator C K j) (denominator C K j)

@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (factor C K j) = factor (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [factor]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (numerator C K j) = numerator (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (denominator C K j) = denominator (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [denominator]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (value C K j) = value (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [value]

theorem numerator_zero (C K : PTm n) : Γ ⊢[PRAAx] numerator C K zero ≐ one := by
  have h := rec_zero (Γ := Γ) (one : PTm 2) numeratorStep ![C,K]
  have e : (Fin.cases zero ![C,K] : Fin 3 → PTm n) = ![zero,C,K] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa [numerator,numeratorF,ap3] using h

theorem denominator_zero (C K : PTm n) : Γ ⊢[PRAAx] denominator C K zero ≐ one := by
  have h := rec_zero (Γ := Γ) (one : PTm 2) denominatorStep ![C,K]
  have e : (Fin.cases zero ![C,K] : Fin 3 → PTm n) = ![zero,C,K] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa [denominator,denominatorF,ap3] using h

theorem numerator_succ (C K j : PTm n) : Γ ⊢[PRAAx]
    numerator C K (succ j) ≐ numerator C K j*factor C K j := by
  have h := rec_succ (Γ := Γ) (one : PTm 2) numeratorStep j ![C,K]
  have a : (Fin.cases (succ j) ![C,K] : Fin 3 → PTm n) = ![succ j,C,K] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases j (Fin.cases (PTm.app (recDef (one : PTm 2) numeratorStep) (Fin.cases j ![C,K])) ![C,K]) :
      Fin 4 → PTm n) = ![j,numerator C K j,C,K] := by funext i; fin_cases i <;> rfl
  rw [a,b] at h
  simpa [numerator,numeratorF,numeratorStep,ap3] using h

theorem denominator_succ (C K j : PTm n) : Γ ⊢[PRAAx]
    denominator C K (succ j) ≐ denominator C K j*pw K j := by
  have h := rec_succ (Γ := Γ) (one : PTm 2) denominatorStep j ![C,K]
  have a : (Fin.cases (succ j) ![C,K] : Fin 3 → PTm n) = ![succ j,C,K] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases j (Fin.cases (PTm.app (recDef (one : PTm 2) denominatorStep) (Fin.cases j ![C,K])) ![C,K]) :
      Fin 4 → PTm n) = ![j,denominator C K j,C,K] := by funext i; fin_cases i <;> rfl
  rw [a,b] at h
  simpa [denominator,denominatorF,denominatorStep,ap3,pw] using h

theorem factor_lower (C K j : PTm n) : Γ ⊢[PRAAx] le (pw K j) (factor C K j) := le_add_right _ _
theorem predecessor_le (K : PTm n) : Γ ⊢[PRAAx] le (pred K) K := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact le_congr ((congrPred Prf.hyp0).eqTrans pred_zero).eqSymm Prf.hyp0.eqSymm (le_refl zero)
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_succ_self (pred K))
theorem factor_upper (C K j : PTm n) : Γ ⊢[PRAAx] le (factor C K j) (pw K j*(one+C)) :=
  le_congr (.eqRefl _) (by ipra_ring)
    (add_le_add₂ (le_refl _) (le_congr (mul_comm _ _) (mul_comm _ _)
      (mul_le_mul_right C (pw_le_pw j (predecessor_le K)))))

theorem denominator_positive (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    le one (denominator C K j) := by
  have hK' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by
    simpa [Fm.shift,Syn.shift] using hK.shift
  have all : Γ ⊢[PRAAx] .all (le one (denominator (Syn.shift C) (Syn.shift K) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,subst_denominator,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (.eqRefl _) (denominator_zero C K).eqSymm (le_refl one)
    · simp only [subst_le,subst_denominator,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact le_congr (.eqRefl _) (denominator_succ _ _ _).eqSymm
        (positive_product _ _ Prf.hyp0 (RationalNonnegativePowers.denominator_positive _ _ hK'.wk))
  simpa only [subst_le,subst_denominator,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

/-- This native comparison includes the total K=0 program. -/
theorem denominator_le_numerator (C K j : PTm n) : Γ ⊢[PRAAx]
    le (denominator C K j) (numerator C K j) := by
  have all : Γ ⊢[PRAAx] .all (le (denominator (Syn.shift C) (Syn.shift K) (var 0))
      (numerator (Syn.shift C) (Syn.shift K) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,subst_denominator,subst_numerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (denominator_zero C K).eqSymm (numerator_zero C K).eqSymm (le_refl one)
    · simp only [subst_le,subst_denominator,subst_numerator,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact le_congr (denominator_succ _ _ _).eqSymm (numerator_succ _ _ _).eqSymm
        (le_mul_mono Prf.hyp0 (factor_lower _ _ _))
  simpa only [subst_le,subst_denominator,subst_numerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem numerator_positive (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    le one (numerator C K j) := le_trans (denominator_positive C K j hK) (denominator_le_numerator C K j)

/-- Actual multiplication at each stage derives the full prefix bound. -/
theorem prefix_bound (C K j : PTm n) : Γ ⊢[PRAAx]
    le (numerator C K j) (denominator C K j*pw (one+C) j) := by
  have all : Γ ⊢[PRAAx] .all (le (numerator (Syn.shift C) (Syn.shift K) (var 0))
      (denominator (Syn.shift C) (Syn.shift K) (var 0)*pw (one+Syn.shift C) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,subst_numerator,subst_denominator,subst_ap2,PTm.subst_add,PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (numerator_zero C K).eqSymm
        ((congrMul (denominator_zero C K) (pw_zero (one+C))).eqTrans (one_mul one)).eqSymm (le_refl one)
    · simp only [subst_le,subst_numerator,subst_denominator,subst_ap2,PTm.subst_add,PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := le (numerator (Syn.shift C) (Syn.shift K) (var 0))
        (denominator (Syn.shift C) (Syn.shift K) (var 0)*pw (one+Syn.shift C) (var 0)) :: Γ.map Fm.shift
      have growing : Δ ⊢[PRAAx] le
          (numerator (Syn.shift C) (Syn.shift K) (var 0)*factor (Syn.shift C) (Syn.shift K) (var 0))
          ((denominator (Syn.shift C) (Syn.shift K) (var 0)*pw (one+Syn.shift C) (var 0))*
            (pw (Syn.shift K) (var 0)*(one+Syn.shift C))) :=
        le_mul_mono Prf.hyp0 (factor_upper _ _ _)
      apply le_congr (numerator_succ _ _ _).eqSymm ?_ growing
      have ds := natEq (denominator_succ (Γ := Δ) (Syn.shift C) (Syn.shift K) (var 0))
      have ps := natEq (pw_succ (Γ := Δ) (one+Syn.shift C) (var 0))
      apply deriveNat
      ipra_simps
      rw [ds,ps]
      ring
  simpa only [subst_le,subst_numerator,subst_denominator,subst_ap2,PTm.subst_add,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem value_zero (C K : PTm n) : Γ ⊢[PRAAx] value C K zero ≐ fraction one one :=
  RationalNonnegativePowers.fraction_congr (numerator_zero C K) (denominator_zero C K)

theorem value_represents (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (value C K j) (ZT.ofNat (numerator C K j)) (denominator C K j) :=
  fraction_represents _ _ (denominator_positive C K j hK)

theorem value_canonical (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (value C K j) := RationalNormalForm.normalize_well_formed _ _ (denominator_positive C K j hK)

theorem value_ge_one (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    rationalLE (fraction one one) (value C K j) :=
  fraction_order _ _ _ _ (le_refl one) (denominator_positive C K j hK)
    (le_congr (by ipra_ring) (by ipra_ring) (denominator_le_numerator C K j))

theorem value_prefix_bound (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    rationalLE (value C K j) (fraction (pw (one+C) j) one) :=
  fraction_order _ _ _ _ (denominator_positive C K j hK) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (prefix_bound C K j))

/-- The actual integer factor gives exactly 1+C*rho^j after clearing. -/
theorem factor_fraction (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    fraction (factor C K j) (pw K j) ≐ RationalArithmetic.add (fraction one one)
      (RationalArithmetic.multiply (fraction C one) (power (pred K) K j)) := by
  have hP := RationalNonnegativePowers.denominator_positive (Γ := Γ) K j hK
  have rightValue := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _
    (fraction_represents one one (le_refl one))
    (RationalRepresentations.represents_multiply _ _ _ _ _ _
      (fraction_represents C one (le_refl one)) (RationalNonnegativePowers.power_represents (pred K) K j hK))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hP) (RationalArithmetic.add_guard _ _)
    (fraction_represents _ _ hP) rightValue hP
    (positive_product _ _ (le_refl one) (positive_product _ _ (le_refl one) hP))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  unfold factor
  ipra_simps
  ring

theorem value_succ_fraction (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    value C K (succ j) ≐ RationalArithmetic.multiply (value C K j) (fraction (factor C K j) (pw K j)) :=
  (RationalNonnegativePowers.fraction_congr (numerator_succ C K j) (denominator_succ C K j)).eqTrans
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (denominator_positive C K j hK)
      (RationalNonnegativePowers.denominator_positive K j hK)).eqSymm

theorem value_recurrence (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    value C K (succ j) ≐ RationalArithmetic.multiply (value C K j)
      (RationalArithmetic.add (fraction one one)
        (RationalArithmetic.multiply (fraction C one) (power (pred K) K j))) :=
  (value_succ_fraction C K j hK).eqTrans (RationalAlgebra.multiply_congr (.eqRefl _) (factor_fraction C K j hK))

def output (C K j : PTm n) : PTm n := pairT (numerator C K j)
  (pairT (denominator C K j) (pairT (value C K j) (factor C K j)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C K j : PTm n) : PTm n := ap3 outputF C K j

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (output C K j) = output (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C K j : PTm n) :
    Syn.subst σ (run C K j) = run (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ j) := by simp [run]

theorem program_at (C K j : PTm n) : Γ ⊢[PRAAx] run C K j ≐ output C K j := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,K,j]
theorem returned_numerator (C K j : PTm n) : Γ ⊢[PRAAx] fstT (run C K j) ≐ numerator C K j :=
  (congrFst (program_at C K j)).eqTrans (fst_pair _ _)
theorem returned_denominator (C K j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C K j)) ≐ denominator C K j :=
  (congrFst ((congrSnd (program_at C K j)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_value (C K j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C K j))) ≐ value C K j :=
  (congrFst ((congrSnd ((congrSnd (program_at C K j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_factor (C K j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run C K j))) ≐ factor C K j :=
  (congrSnd ((congrSnd ((congrSnd (program_at C K j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_prefix_bound (C K j : PTm n) : Γ ⊢[PRAAx]
    le (fstT (run C K j)) (fstT (sndT (run C K j))*pw (one+C) j) :=
  le_congr (returned_numerator C K j).eqSymm (congrMul (returned_denominator C K j).eqSymm (.eqRefl _))
    (prefix_bound C K j)

theorem actual_geometric_product_recurrences_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((numerator (var 0) (var 1) zero ≐ one) ⋏ ((denominator (var 0) (var 1) zero ≐ one) ⋏
      ((numerator (var 0) (var 1) (succ (var 2)) ≐ numerator (var 0) (var 1) (var 2)*factor (var 0) (var 1) (var 2)) ⋏
        denominator (var 0) (var 1) (succ (var 2)) ≐ denominator (var 0) (var 1) (var 2)*pw (var 1) (var 2)))) :=
  closeUniv 3 (.andI (numerator_zero _ _) (.andI (denominator_zero _ _) (.andI (numerator_succ _ _ _) (denominator_succ _ _ _))))

theorem actual_geometric_product_native_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le (denominator (var 0) (var 1) (var 2)) (numerator (var 0) (var 1) (var 2))) ⋏
      le (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2)*pw (one+var 0) (var 2))) :=
  closeUniv 3 (.andI (denominator_le_numerator _ _ _) (prefix_bound _ _ _))

theorem actual_geometric_product_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ (le one (denominator (var 0) (var 1) (var 2)) ⋏ le one (numerator (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (denominator_positive _ _ _ Prf.hyp0) (numerator_positive _ _ _ Prf.hyp0)))

theorem actual_geometric_product_value_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ value (var 0) (var 1) (succ (var 2)) ≐ RationalArithmetic.multiply (value (var 0) (var 1) (var 2))
      (RationalArithmetic.add (fraction one one)
        (RationalArithmetic.multiply (fraction (var 0) one) (power (pred (var 1)) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (value_recurrence _ _ _ Prf.hyp0))

theorem actual_geometric_product_rational_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (rationalLE (fraction one one) (value (var 0) (var 1) (var 2)) ⋏
        rationalLE (value (var 0) (var 1) (var 2)) (fraction (pw (one+var 0) (var 2)) one))) :=
  closeUniv 3 (.impI (.andI (value_ge_one _ _ _ Prf.hyp0) (value_prefix_bound _ _ _ Prf.hyp0)))

theorem actual_geometric_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      le (fstT (run (var 0) (var 1) (var 2)))
        (fstT (sndT (run (var 0) (var 1) (var 2)))*pw (one+var 0) (var 2))) :=
  closeUniv 3 (.andI (program_at _ _ _) (returned_prefix_bound _ _ _))

end LeanProofs.IPRA.Analysis.GaussianGeometricProduct
