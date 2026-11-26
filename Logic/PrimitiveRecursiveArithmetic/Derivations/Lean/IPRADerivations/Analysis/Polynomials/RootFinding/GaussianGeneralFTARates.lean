import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGeneralFTAConstants
import IPRADerivations.Algebra.FTABounds
import IPRADerivations.Core.LinearCombination

/-!
# Exact computed rates of the general coefficient-name FTA

The source q, Q and rho are actual normalized rational programs. The
finite Bernoulli theorem proves Q<=rho^N from the computed K=8ND,
not from an incoming rate law. The block and arbitrary dyadic estimates
reuse the checked finite decay theorem. Exact canonical scalar arithmetic
also binds q+1/(8D)=Q and q squared to the existing local RD contract.
Every degree and block count remains an internal numerical variable.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTARates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants
  (D qDen qNum q QDen QNum K rhoNum rho qDen_positive QDen_positive QDen_lower K_positive K_lower)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Analysis.RationalNonnegativePowers (power denominator_positive)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem predecessor_form (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    M ≐ pred M+one :=
  (RationalIntegerNormalization.positive_form hM).eqTrans (succ_eq_add_one _)

theorem predecessor_positive (M : PTm n) (hM : Γ ⊢[PRAAx] le two M) : Γ ⊢[PRAAx] le one (pred M) :=
  (succ_monus_succ one (pred M)).eqSymm.eqTrans
    (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form (le_trans (le_succ_self one) hM)) hM)

theorem predecessor_below (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] lt (pred M) M :=
  le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hM).eqSymm (le_refl (succ (pred M)))

theorem qDen_lower (N : PTm n) : Γ ⊢[PRAAx] le two (qDen N) := by
  have four : Γ ⊢[PRAAx] le two (two*two) :=
    le_congr (one_mul two) (.eqRefl _) (mul_le_mul_right two (le_succ_self one))
  exact le_congr ((mul_comm two one).eqTrans (one_mul two)) (GaussianGeneralFTAConstants.qDen_value N).eqSymm
    (le_mul_mono four (GaussianGeneralFTAConstants.D_positive N))

theorem qNum_positive (N : PTm n) : Γ ⊢[PRAAx] le one (qNum N) := predecessor_positive _ (qDen_lower N)
theorem QNum_positive (N : PTm n) : Γ ⊢[PRAAx] le one (QNum N) := predecessor_positive _ (QDen_lower N)
theorem rhoNum_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (rhoNum N) :=
  predecessor_positive _ (K_lower N hN)
theorem qNum_below (N : PTm n) : Γ ⊢[PRAAx] lt (qNum N) (qDen N) := predecessor_below _ (qDen_positive N)
theorem QNum_below (N : PTm n) : Γ ⊢[PRAAx] lt (QNum N) (QDen N) := predecessor_below _ (QDen_positive N)
theorem rhoNum_below (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] lt (rhoNum N) (K N) :=
  predecessor_below _ (K_positive N hN)

theorem ratio_le_one (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    rationalLE (fraction (pred M) M) (fraction one one) :=
  fraction_order _ _ _ _ hM (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) (le_of_lt (predecessor_below M hM)))
theorem q_le_one (N : PTm n) : Γ ⊢[PRAAx] rationalLE (q N) (fraction one one) := ratio_le_one _ (qDen_positive N)
theorem Q_le_one (N : PTm n) : Γ ⊢[PRAAx] rationalLE (GaussianGeneralFTAConstants.Q N) (fraction one one) := ratio_le_one _ (QDen_positive N)
theorem rho_le_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (rho N) (fraction one one) := ratio_le_one _ (K_positive N hN)

theorem half_cross (M : PTm n) (hM : Γ ⊢[PRAAx] le two M) : Γ ⊢[PRAAx] le M (two*pred M) :=
  le_congr ((add_comm _ _).eqTrans (predecessor_form M (le_trans (le_succ_self one) hM)).eqSymm)
    (by ipra_ring) (add_le_add_right (pred M) (predecessor_positive M hM))

theorem half_le_Q (N : PTm n) : Γ ⊢[PRAAx] rationalLE (fraction one two) (GaussianGeneralFTAConstants.Q N) := by
  have crossed : Γ ⊢[PRAAx] le (QDen N) (two*QNum N) := half_cross _ (QDen_lower N)
  exact fraction_order _ _ _ _ (le_succ_self one) (QDen_positive N)
    (le_congr (by ipra_ring) (by ipra_ring) crossed)

/-- The native gap follows from the actual computed K=N*(8D). -/
theorem K_gap (N : PTm n) : Γ ⊢[PRAAx] monus (K N) N ≐ N*QNum N := by
  have h : Γ ⊢[PRAAx] QDen N ≐ QNum N+one := predecessor_form (Γ := Γ) (QDen N) (QDen_positive N)
  have e : Γ ⊢[PRAAx] K N ≐ N*QNum N+N :=
    (congrMul (.eqRefl N) h).eqTrans (by ipra_ring)
  exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)

/-- This is the source Bernoulli comparison on the original normalized rates. -/
theorem Q_le_rho_power (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (GaussianGeneralFTAConstants.Q N) (power (rhoNum N) (K N) N) := by
  have hK := K_positive N hN
  have shape : Γ ⊢[PRAAx] succ (rhoNum N) ≐ K N := (RationalIntegerNormalization.positive_form hK).eqSymm
  have raw : Γ ⊢[PRAAx] le (pw (K N) N*monus (K N) N) (K N*pw (rhoNum N) N) :=
    le_congr (congrMul (congrAp2 powF (.eqRefl N) shape) (congrMonus shape (.eqRefl N)))
      (congrMul shape (.eqRefl _)) (Algebra.FTABounds.bernoulli_down (rhoNum N) N)
  have gap := le_congr (congrMul (.eqRefl _) (K_gap N)) (.eqRefl _) raw
  have factored : Γ ⊢[PRAAx] le (N*(pw (K N) N*QNum N)) (N*(QDen N*pw (rhoNum N) N)) :=
    le_congr (by ipra_ring) (by unfold K; ipra_ring) gap
  exact fraction_order _ _ _ _ (QDen_positive N) (denominator_positive (K N) N hK)
    (le_congr (.eqRefl _) (mul_comm _ _) (RationalValueBounds.positive_cancel hN factored))

theorem Q_le_rho (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (GaussianGeneralFTAConstants.Q N) (rho N) :=
  RationalArgmin.transitive (Q_le_rho_power N hN)
    (RationalArgmin.rationalLE_congr (.eqRefl _) (RationalNonnegativePowers.power_one _ _)
      (RationalNonnegativePowerOrder.power_exponent_antitone _ _ one N (K_positive N hN)
        (le_of_lt (rhoNum_below N hN)) hN))

theorem rho_block_half (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (power (rhoNum N) (K N) (K N)) (fraction one two) :=
  fraction_order _ _ _ _ (denominator_positive _ _ (K_positive N hN)) (le_succ_self one)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianDescentClockArithmetic.block_decay (K N) (K_positive N hN)))

theorem rho_dyadic (N m : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (power (rhoNum N) (K N) (K N*m)) (fraction one (pw two m)) :=
  fraction_order _ _ _ _ (denominator_positive _ _ (K_positive N hN)) (denominator_positive two m (le_succ_self one))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianDescentClockArithmetic.dyadic_decay (K N) m (K_positive N hN)))

theorem q_square_clock (N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (q N) (q N) ≐ GaussianDescentClock.contractionSquare N :=
  RationalNonnegativePowers.fraction_multiply _ _ _ _ (qDen_positive N) (qDen_positive N)

/-- Exact canonical scalar addition, with the independent actual fractions. -/
theorem q_plus_drift (N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.add (q N) (fraction one (QDen N)) ≐ GaussianGeneralFTAConstants.Q N := by
  have hq := qDen_positive (Γ := Γ) N
  have hQ := QDen_positive (Γ := Γ) N
  have left := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (qNum N) (qDen N) hq) (fraction_represents one (QDen N) hQ)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hQ) left (fraction_represents _ _ hQ)
    (positive_product _ _ hq hQ) hQ
  have a : Γ ⊢[PRAAx] qDen N ≐ qNum N+one := predecessor_form _ hq
  have b : Γ ⊢[PRAAx] QDen N ≐ QNum N+one := predecessor_form _ hQ
  have c : Γ ⊢[PRAAx] QDen N ≐ two*qDen N := .eqRefl _
  ipra_lc -𝔞(QDen N)*𝔞(QDen N)*natEq a+𝔞(qDen N)*𝔞(QDen N)*natEq b-𝔞(QDen N)*natEq c

def output (N : PTm n) : PTm n := pairT (q N) (pairT (GaussianGeneralFTAConstants.Q N) (rho N))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (N : PTm n) : PTm n := ap1 outputF N
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (output N) = output (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (run N) = run (Syn.subst σ N) := by simp [run]
theorem program_at (N : PTm n) : Γ ⊢[PRAAx] run N ≐ output N := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![N]
theorem returned_q (N : PTm n) : Γ ⊢[PRAAx] fstT (run N) ≐ q N :=
  (congrFst (program_at N)).eqTrans (fst_pair _ _)
theorem returned_Q (N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run N)) ≐ GaussianGeneralFTAConstants.Q N :=
  (congrFst ((congrSnd (program_at N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_rho (N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run N)) ≐ rho N :=
  (congrSnd ((congrSnd (program_at N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem computed_general_fta_rate_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶
      ((le one (qNum (var 0)) ⋏ lt (qNum (var 0)) (qDen (var 0))) ⋏
        ((le one (QNum (var 0)) ⋏ lt (QNum (var 0)) (QDen (var 0))) ⋏
          (le one (rhoNum (var 0)) ⋏ lt (rhoNum (var 0)) (K (var 0)))))) :=
  closeUniv 1 (.impI (.andI (.andI (qNum_positive _) (qNum_below _))
    (.andI (.andI (QNum_positive _) (QNum_below _)) (.andI (rhoNum_positive _ Prf.hyp0) (rhoNum_below _ Prf.hyp0)))))

theorem computed_general_fta_rate_comparisons_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶
      (rationalLE (fraction one two) (GaussianGeneralFTAConstants.Q (var 0)) ⋏
        (rationalLE (GaussianGeneralFTAConstants.Q (var 0)) (power (rhoNum (var 0)) (K (var 0)) (var 0)) ⋏
          (rationalLE (rho (var 0)) (fraction one one) ⋏ rationalLE (GaussianGeneralFTAConstants.Q (var 0)) (rho (var 0)))))) :=
  closeUniv 1 (.impI (.andI (half_le_Q _) (.andI (Q_le_rho_power _ Prf.hyp0)
    (.andI (rho_le_one _ Prf.hyp0) (Q_le_rho _ Prf.hyp0)))))

theorem exact_general_fta_drift_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((RationalArithmetic.add (q (var 0)) (fraction one (QDen (var 0))) ≐ GaussianGeneralFTAConstants.Q (var 0)) ⋏
      RationalArithmetic.multiply (q (var 0)) (q (var 0)) ≐ GaussianDescentClock.contractionSquare (var 0)) :=
  closeUniv 1 (.andI (q_plus_drift _) (q_square_clock _))

theorem computed_general_fta_dyadic_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ rationalLE (power (rhoNum (var 0)) (K (var 0)) (K (var 0)*var 1))
      (fraction one (pw two (var 1)))) :=
  closeUniv 2 (.impI (rho_dyadic _ _ Prf.hyp0))

theorem actual_general_fta_rates_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((run (var 0) ≐ output (var 0)) ⋏
      ((fstT (run (var 0)) ≐ q (var 0)) ⋏
        ((fstT (sndT (run (var 0))) ≐ GaussianGeneralFTAConstants.Q (var 0)) ⋏
          sndT (sndT (run (var 0))) ≐ rho (var 0)))) :=
  closeUniv 1 (.andI (program_at _) (.andI (returned_q _) (.andI (returned_Q _) (returned_rho _))))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTARates
